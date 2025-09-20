import CombinatorialGames.Mathlib.Neg
import CombinatorialGames.Mathlib.Small
import CombinatorialGames.Player
import CombinatorialGames.Outcome
import Mathlib.Algebra.Group.Pointwise.Set.Basic

universe u v

-- Implementation detail
def Moves.IsOption' {G : Type v} (moves : Player → G → Set G) (x y : G) : Prop :=
   x ∈ ⋃ p, moves p y

class Moves (G : Type v) where
  moves (p : Player) (x : G) : Set G
  isOption'_wf : WellFounded (Moves.IsOption' moves)

class Form (G : Type v) extends Moves G, InvolutiveNeg G, Add G where
  moves_neg (p : Player) (x : G) : moves p (-x) = Set.neg.neg (moves (-p) x)
  moves_add (p : Player) (x y : G) : moves p (x + y) = (· + y) '' moves p x ∪ (x + ·) '' moves p y

namespace Moves

variable {G : Type u} [g_moves : Moves G]

/-- `IsOption x y` means that `x` is either a left or a right move for `y`. -/
def IsOption (x y : G) : Prop := IsOption' g_moves.moves x y

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

instance (x : G) : Small.{u} {y // IsOption y x} :=
  inferInstanceAs (Small (⋃ p, moves p x))

theorem isOption_wf : WellFounded (@IsOption G _) := g_moves.isOption'_wf

instance : IsWellFounded _ (@IsOption G _) := ⟨isOption_wf⟩

theorem IsOption.irrefl (x : G) : ¬ IsOption x x := _root_.irrefl x

theorem self_notMem_moves (p : Player) (x : G) : x ∉ moves p x :=
  fun hx ↦ IsOption.irrefl x (.of_mem_moves hx)

/-- A (proper) subposition is any game in the transitive closure of `IsOption`. -/
def Subposition : G → G → Prop :=
  Relation.TransGen IsOption

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_moves {p} {x y : G} (h : x ∈ moves p y) : Subposition x y :=
  Relation.TransGen.single (.of_mem_moves h)

theorem Subposition.trans {x y z : G} (h₁ : Subposition x y) (h₂ : Subposition y z) :
    Subposition x z :=
  Relation.TransGen.trans h₁ h₂

instance (x : G) : Small.{u} {y // Subposition y x} :=
  small_transGen' _ x

instance : IsTrans _ (@Subposition G _) := inferInstanceAs (IsTrans _ (Relation.TransGen _))
instance : IsWellFounded _ (@Subposition G _) := inferInstanceAs (IsWellFounded _ (Relation.TransGen _))
instance : WellFoundedRelation G := ⟨Subposition, instIsWellFoundedSubposition.wf⟩

macro "form_wf" : tactic =>
  `(tactic| all_goals solve_by_elim (maxDepth := 8)
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subposition.of_mem_moves, Subposition.trans, Subtype.prop] )

def IsEnd (p : Player) (g : G) := moves p g = ∅

end Moves

namespace Form

export Moves (IsOption IsOption.iff_mem_union IsOption.of_mem_moves Subposition moves IsEnd)

variable {G : Type u} [g_form : Form G]

theorem exists_moves_neg {P : G → Prop} {p : Player} {x : G} :
    (∃ y ∈ Moves.moves p (-x), P y) ↔ (∃ y ∈ Moves.moves (-p) x, P (-y)) := by
  simp only [Form.moves_neg, Set.mem_neg, Set.exists_mem_neg]

theorem IsEnd.add_iff {g h : G} {p : Player} :
    IsEnd p (g + h) ↔ (IsEnd p g ∧ IsEnd p h) := by
  constructor <;> intro h1
  · unfold IsEnd at *
    simp only [moves_add, Set.union_empty_iff, Set.image_eq_empty] at h1
    exact h1
  · unfold IsEnd at h1
    simp only [IsEnd, moves_add, Set.union_empty_iff, Set.image_eq_empty]
    exact h1

end Form

class MisereForm (G : Type v) extends Form G where
  WinsGoingFirst (p : Player) (g : G) : Prop

namespace MisereForm

variable {G : Type u} [g_form : MisereForm G]

open scoped Classical in
noncomputable def MiserePlayerOutcome : G → Player → Player :=
  fun g p => if WinsGoingFirst p g then p else -p

open scoped Classical in
noncomputable def MisereOutcome : G → Outcome :=
  fun g => Outcome.ofPlayers (MiserePlayerOutcome g .left) (MiserePlayerOutcome g .right)

end MisereForm
