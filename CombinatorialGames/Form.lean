module

public import CombinatorialGames.Mathlib.Small
public import CombinatorialGames.Outcome
public import CombinatorialGames.Player
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Logic.Small.Defs
public import Mathlib.Order.SetNotation

universe u v

public section

-- Implementation detail
@[expose] def Moves.IsOption' {G : Type v} (moves : Player → G → Set G) (x y : G) : Prop :=
   x ∈ ⋃ p, moves p y

class Moves (G : Type v) where
  moves (p : Player) (x : G) : Set G
  isOption'_wf : WellFounded (Moves.IsOption' moves)

class Form (G : Type (v + 1)) extends Moves G, InvolutiveNeg G, SubtractionCommMonoid G, AddCommMonoidWithOne G where
  moves_neg' (p : Player) (x : G) : moves p (-x) = Set.neg.neg (moves (-p) x)
  moves_add' (p : Player) (x y : G) : moves p (x + y) = (· + y) '' moves p x ∪ (x + ·) '' moves p y
  moves_zero' (p : Player) : moves p 0 = ∅
  moves_small' (p : Player) (x : G) : Small.{v} (moves p x)
  IsEndLike (p : Player) (x : G) : Prop
  IsEndLike_ofEnd' (p : Player) (x : G) (h1 : moves p x = ∅) : IsEndLike p x
  IsEndLike_add_iff' (p : Player) (x y : G) : IsEndLike p (x + y) ↔ IsEndLike p x ∧ IsEndLike p y
  IsEndLike_neg_iff_neg' (p : Player) (g : G) : IsEndLike p (-g) ↔ IsEndLike (-p) g

namespace Moves

variable {G : Type (u + 1)} [g_moves : Moves G]

/-- `IsOption x y` means that `x` is either a left or a right move for `y`. -/
@[expose] def IsOption (x y : G) : Prop := IsOption' g_moves.moves x y

-- /-- The set of left moves of the game. -/
-- scoped notation:max g:max "ᴸ" => Form.moves Player.left g

-- /-- The set of right moves of the game. -/
-- scoped notation:max g:max "ᴿ" => Form.moves Player.right g

@[aesop simp]
lemma IsOption.iff_mem_union {x y : G} :
    IsOption x y ↔ x ∈ moves .left y ∪ moves .right y := by
  simp [IsOption, IsOption', Player.exists]

theorem IsOption.of_mem_moves {x y : G} {p : Player} (h : x ∈ moves p y) :
    IsOption x y := ⟨_, ⟨p, rfl⟩, h⟩

instance (x : G) : Small.{u + 1} {y // IsOption y x} :=
  inferInstanceAs (Small (⋃ p, moves p x))

theorem isOption_wf : WellFounded (@IsOption G _) := g_moves.isOption'_wf

instance : IsWellFounded _ (@IsOption G _) := ⟨isOption_wf⟩

theorem IsOption.irrefl (x : G) : ¬ IsOption x x := _root_.irrefl x

theorem self_notMem_moves (p : Player) (x : G) : x ∉ moves p x :=
  fun hx ↦ IsOption.irrefl x (.of_mem_moves hx)

/-- A (proper) subposition is any game in the transitive closure of `IsOption`. -/
@[expose] def Subposition : G → G → Prop :=
  Relation.TransGen IsOption

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_moves {p} {x y : G} (h : x ∈ moves p y) : Subposition x y :=
  Relation.TransGen.single (.of_mem_moves h)

theorem Subposition.trans {x y z : G} (h₁ : Subposition x y) (h₂ : Subposition y z) :
    Subposition x z :=
  Relation.TransGen.trans h₁ h₂

instance (x : G) : Small.{u + 1} {y // Subposition y x} :=
  small_transGen' _ x

instance : IsTrans _ (@Subposition G _) := inferInstanceAs (IsTrans _ (Relation.TransGen _))
instance : IsWellFounded _ (@Subposition G _) := inferInstanceAs (IsWellFounded _ (Relation.TransGen _))
instance : WellFoundedRelation G := ⟨Subposition, instIsWellFoundedSubposition.wf⟩

macro "form_wf" : tactic =>
  `(tactic| all_goals solve_by_elim (maxDepth := 8)
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subposition.of_mem_moves, Subposition.trans, Subtype.prop] )

end Moves

namespace Form

export Moves (IsOption IsOption.iff_mem_union IsOption.of_mem_moves Subposition moves)

def IsEnd {G : Type (u + 1)} [Moves G] (p : Player) (g : G) := moves p g = ∅

theorem IsEnd_def {G : Type (u + 1)} [Moves G] (p : Player) (g : G) : IsEnd p g = (moves p g = ∅) := by rfl

variable {G : Type (u + 1)} [g_form : Form G]

protected theorem IsEnd.IsEndLike {p : Player} {x : G} (h1 : IsEnd p x) : IsEndLike p x :=
  IsEndLike_ofEnd' p x h1

@[simp]
protected theorem IsEndLike.add_iff {p : Player} {x y : G}
    : IsEndLike p (x + y) ↔ IsEndLike p x ∧ IsEndLike p y := IsEndLike_add_iff' p x y

@[simp]
protected theorem IsEndLike.neg_iff_neg {g : G} {p : Player} : IsEndLike p (-g) ↔ IsEndLike (-p) g :=
  IsEndLike_neg_iff_neg' p g

@[simp]
theorem moves_neg (p : Player) (x : G) : moves p (-x) = Set.neg.neg (moves (-p) x) :=
  moves_neg' p x

@[simp]
theorem moves_add (p : Player) (x y : G) : moves p (x + y) = (· + y) '' moves p x ∪ (x + ·) '' moves p y :=
  moves_add' p x y

@[simp]
theorem moves_zero (p : Player) : @moves G _ p 0 = ∅ :=
  moves_zero' p

@[simp]
theorem zero_IsEnd (p : Player) : IsEnd p (0 : G) := moves_zero p

@[simp]
theorem moves_small (p : Player) (x : G) : Small.{u} (moves p x) :=
  moves_small' p x

theorem exists_moves_neg {P : G → Prop} {p : Player} {x : G} :
    (∃ y ∈ Moves.moves p (-x), P y) ↔ (∃ y ∈ Moves.moves (-p) x, P (-y)) := by
  simp only [moves_neg, Set.mem_neg, Set.exists_neg_mem]

@[simp]
theorem IsEnd.add_iff {g h : G} {p : Player} :
    IsEnd p (g + h) ↔ (IsEnd p g ∧ IsEnd p h) := by
  constructor <;> intro h1
  · unfold IsEnd at *
    simp only [moves_add, Set.union_empty_iff, Set.image_eq_empty] at h1
    exact h1
  · unfold IsEnd at h1
    simp only [IsEnd, moves_add, Set.union_empty_iff, Set.image_eq_empty]
    exact h1

theorem IsEnd_neg_iff_neg {g : G} {p : Player} : IsEnd p (-g) ↔ IsEnd (-p) g := by
  constructor <;> cases p
  all_goals
  · intro h1
    simp only [IsEnd, moves_neg, Set.neg_eq_empty] at *
    exact h1

@[simp]
theorem IsEnd_zero {p : Player} : IsEnd p (0 : G) := by
  rw [IsEnd, moves_zero]

theorem mem_moves_ne_zero {g gl : G} {p : Player} (h1 : gl ∈ moves p g) : g ≠ 0 := by
  intro h2
  simp only [h2, moves_zero, Set.mem_empty_iff_false] at h1

theorem not_IsEnd_ne_zero {g : G} {p : Player} (h1 : ¬(IsEnd p g)) : g ≠ 0 := by
  intro h2
  rw [h2] at h1
  exact h1 IsEnd_zero

theorem not_IsEnd_exists_move {g : G} {p : Player}
    (h1 : ¬IsEnd p g) :
    ∃ gp, gp ∈ moves p g := by
  unfold IsEnd at h1
  by_contra h4
  simp only [not_exists] at h4
  absurd h1
  exact Set.subset_eq_empty h4 rfl

@[simp]
theorem IsEnd.not_mem_moves {g gp : G} {p : Player} (h1 : IsEnd p g) : gp ∉ moves p g := by
  rw [IsEnd_def] at h1
  simp [h1]

theorem add_left_mem_moves_add {p : Player} {x y : G} (h : x ∈ moves p y) (z : G) :
    z + x ∈ moves p (z + y) := by
  rw [moves_add]; right; use x

theorem add_right_mem_moves_add {p : Player} {x y : G} (h : x ∈ moves p y) (z : G) :
    x + z ∈ moves p (y + z) := by
  rw [moves_add]; left; use x

theorem sub_left_mem_moves_sub {p : Player} {x y : G} (h : x ∈ moves p y) (z : G) :
    z - x ∈ moves (-p) (z - y) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply add_left_mem_moves_add;
  simpa [moves_neg]

theorem sub_left_mem_moves_sub_neg {p : Player} {x y : G} (h : x ∈ moves (-p) y) (z : G) :
    z - x ∈ moves p (z - y) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply add_left_mem_moves_add;
  simpa [moves_neg]

theorem sub_right_mem_moves_sub {p : Player} {x y : G} (h : x ∈ moves p y) (z : G) :
    x - z ∈ moves p (y - z) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact add_right_mem_moves_add h _

theorem exists_moves_add {p : Player} {P : G → Prop} {x y : G} :
    (∃ a ∈ moves p (x + y), P a) ↔
      (∃ a ∈ moves p x, P (a + y)) ∨ (∃ b ∈ moves p y, P (x + b)) := by
  aesop

@[aesop simp]
lemma isOption_iff_mem_union {x y : G} : IsOption x y ↔ x ∈ moves .left y ∪ moves .right y := by
  simp [IsOption, Moves.IsOption', Player.exists]

end Form
