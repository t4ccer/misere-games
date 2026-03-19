module

public import CombinatorialGames.OfSets
public import Mathlib.Logic.Small.Set
public import CombinatorialGames.Mathlib.Small
public import CombinatorialGames.Outcome
public import CombinatorialGames.Player
public import Mathlib.Algebra.Group.Pointwise.Set.Small
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.CharZero.Defs
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

class Form (G : Type (v + 1)) extends Moves G, OfSets G fun _ ↦ True, InvolutiveNeg G, AddCommSemigroup G where
  moves_neg' (p : Player) (x : G) : moves p (-x) = Set.neg.neg (moves (-p) x)
  moves_add' (p : Player) (x y : G) : moves p (x + y) = (· + y) '' moves p x ∪ (x + ·) '' moves p y
  moves_small' (p : Player) (x : G) : Small.{v} (moves p x)
  moves_ofSets' (p : Player) (st : Player → Set G) [Small.{v} (st .left)] [Small.{v} (st .right)] : moves p !{st}= st p
  add_zero' (x : G) : x + !{fun _ => ∅} = x
  add_eq_zero_iff' (x y : G) : x + y = !{fun _ => ∅} ↔ x = !{fun _ => ∅} ∧ y = !{fun _ => ∅}
  ofSets_inj'' {st₁ st₂ : Player → Set G}
    [Small (st₁ .left)] [Small (st₁ .right)] [Small (st₂ .left)] [Small (st₂ .right)] :
    !{st₁} = !{st₂} ↔ st₁ = st₂
  neg_ofSets'' (s t : Set G) [Small s] [Small t] : -!{s | t} = !{-t | -s}
  neg_add' (x y : G) : -(x + y) = -x + -y
  smallElemMoves' (p : Player) (x : G) : Small.{v} (moves p x)
  IsEndLike (p : Player) (x : G) : Prop
  ofSets_IsEndLike_iff' (p : Player) (s t : Set G) [Small s] [Small t] : IsEndLike p !{s | t} ↔ moves p !{s | t} = ∅
  ofSets_add_ofSets'' (s₁ t₁ s₂ t₂ : Set G) [Small s₁] [Small t₁] [Small s₂] [Small t₂] : !{s₁ | t₁} + !{s₂ | t₂} = !{(· + !{s₂ | t₂}) '' s₁ ∪ (!{s₁ | t₁} + ·) '' s₂ | (· + !{s₂ | t₂}) '' t₁ ∪ (!{s₁ | t₁} + ·) '' t₂}
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

theorem not_IsEnd_def {G : Type (u + 1)} [Moves G] (p : Player) (g : G) : ¬(IsEnd p g) ↔ (moves p g ≠ ∅) := by
  simp [IsEnd_def]

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

@[simp 900]
theorem moves_add (p : Player) (x y : G) : moves p (x + y) = (· + y) '' moves p x ∪ (x + ·) '' moves p y :=
  moves_add' p x y

instance instSmallElemMoves (p : Player) (x : G) : Small.{u} (moves p x) := smallElemMoves' p x

@[simp]
theorem moves_ofSets (p : Player) (st : Player → Set G) [Small.{u} (st .left)] [Small.{u} (st .right)] : moves p !{st}= st p := moves_ofSets' p st

@[simp]
theorem leftMoves_ofSets (s t : Set G) [Small.{u} s] [Small.{u} t] : moves .left !{s | t} = s :=
  moves_ofSets ..

@[simp]
theorem rightMoves_ofSets (s t : Set G) [Small.{u} s] [Small.{u} t] : moves .right !{s | t} = t :=
  moves_ofSets ..

@[simp]
theorem ofSets_inj' {st₁ st₂ : Player → Set G}
    [Small (st₁ .left)] [Small (st₁ .right)] [Small (st₂ .left)] [Small (st₂ .right)] :
    !{st₁} = !{st₂} ↔ st₁ = st₂ := ofSets_inj''

theorem ofSets_inj {s₁ s₂ t₁ t₂ : Set G} [Small s₁] [Small s₂] [Small t₁] [Small t₂] :
    !{s₁ | t₁} = !{s₂ | t₂} ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp

instance : Zero G := ⟨!{fun _ ↦ ∅}⟩

theorem zero_def : (0 : G) = !{fun _ ↦ ∅} := rfl

@[simp]
theorem moves_zero (p : Player) : moves p (0 : G) = ∅ := by
  simp [zero_def]

@[simp]
theorem zero_IsEnd (p : Player) : IsEnd p (0 : G) := moves_zero p

@[simp]
theorem neg_ofSets (s t : Set G) [Small s] [Small t] : -!{s | t} = !{-t | -s} := neg_ofSets'' s t

@[simp]
theorem neg_ofSets' (s t : Set G) [Small s] [Small t] : -!{s | t} = !{-t | -s} := by
  simp_rw [neg_ofSets]

@[simp]
theorem neg_ofSets_const (s : Set G) [Small s] :
    -!{fun _ ↦ s} = !{fun _ ↦ -s} := by
  rw [ofSets_eq_ofSets_cases, ofSets_eq_ofSets_cases]
  simp
  funext p
  cases p <;> rfl

instance : NegZeroClass G where
  neg_zero := by simp only [zero_def, neg_ofSets_const, Set.neg_empty]

instance : Inhabited G := ⟨0⟩

instance : One G := ⟨!{{0} | ∅}⟩

theorem one_def : (1 : G) = !{{0} | ∅} := rfl

@[simp] theorem leftMoves_one : moves .left (1 : G) = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_one : moves .right (1 : G) = ∅ := rightMoves_ofSets ..

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

instance : AddCommMonoid G where
  add_zero := add_zero'
  zero_add _ := add_comm (G := G) .. ▸ add_zero' _
  add_comm := add_comm
  add_assoc := add_assoc
  nsmul := nsmulRec

instance : SubNegMonoid G where
  zsmul := zsmulRec

instance : AddCommMonoidWithOne G where

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

-- Casts

@[simp, norm_cast] theorem natCast_zero : ((0 : ℕ) : G) = 0 := by simp
@[simp, norm_cast] theorem natCast_one : ((1 : ℕ) : G) = 1 := by simp

theorem leftMoves_natCast_succ' : ∀ n : ℕ, moves .left (n.succ : G) = {(n : G)}
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_succ, moves_add, leftMoves_natCast_succ']
    simp

@[simp 1100]
theorem leftMoves_natCast_succ (n : ℕ) : moves .left ((n + 1) : G) = {(n : G)} := by
  norm_cast
  exact leftMoves_natCast_succ' n

@[simp 1100]
theorem rightMoves_natCast : ∀ n : ℕ, moves .right (n : G) = ∅
  | 0 => by simp [moves_zero]
  | n + 1 => by
    rw [Nat.cast_succ, moves_add, rightMoves_natCast]
    simp

@[simp 1100]
theorem leftMoves_ofNat (n : ℕ) [n.AtLeastTwo] : moves .left (ofNat(n) : G) = {((n - 1 : ℕ) : G)} := by
  change moves .left (n : G) = _
  rw [← Nat.succ_pred (NeZero.out (n := n)), leftMoves_natCast_succ']
  simp

@[simp 1100]
theorem rightMoves_ofNat (n : ℕ) [n.AtLeastTwo] : moves .right (ofNat(n) : G) = ∅ :=
  rightMoves_natCast n

instance : IntCast G where
  intCast
  | .ofNat n => n
  | .negSucc n => -(n + 1)

@[simp, norm_cast] theorem intCast_nat (n : ℕ) : ((n : ℤ) : G) = n := rfl

@[simp] theorem intCast_ofNat (n : ℕ) : ((ofNat(n) : ℤ) : G) = n := rfl

@[simp] theorem intCast_negSucc (n : ℕ) : (Int.negSucc n : G) = -(n + 1) := rfl

@[simp, norm_cast] theorem intCast_zero : ((0 : ℤ) : G) = 0 := by simp

@[simp, norm_cast] theorem intCast_one : ((1 : ℤ) : G) = 1 := by simp

@[simp, norm_cast] theorem intCast_neg (n : ℤ) : ((-n : ℤ) : G) = -(n : G) := by
  cases n with
  | ofNat n =>
    induction n with
    | zero => simp
    | succ k ih => rfl
  | negSucc n =>
    simp only [intCast_negSucc, neg_neg, Int.neg_negSucc]
    norm_cast

@[simp]
theorem leftMoves_eq_natCast_zero_lt {a : ℕ} (h1 : 0 < a)
    : moves .left (a : G) = {((a - 1 : ℕ) : G)} := by
  obtain ⟨x, h2⟩ := Nat.exists_add_one_eq.mpr h1
  rw [<-h2, Nat.cast_add, natCast_one, leftMoves_natCast_succ]
  rfl

theorem leftMoves_natCast_zero_lt {a : ℕ} (h1 : 0 < a)
    : ((a - 1 : ℕ) : G) ∈ moves .left (a : G) := by
  simp [h1]

@[simp 1100] -- This should trigger before `leftMoves_add`.
theorem leftMoves_intCast_succ {n : ℤ} (h1 : 0 ≤ n) : moves .left ((n + 1) : G) = {(n : G)} := by
  match n with
  | Int.ofNat n => simp
  | Int.negSucc k => simp

@[simp]
theorem leftMoves_intCast {a : ℤ} (h1 : 0 < a)
    : moves .left (a : G) = {((a - 1 : ℤ) : G)} := by
  obtain ⟨a', h_a'⟩ := (CanLift.prf a h1.le : ∃ (a' : ℕ), a' = a)
  rw [<-h_a']
  have : ∃ x, x + 1 = a' := by use a' - 1; omega
  obtain ⟨x, h2⟩ := this
  rw [<-h2]
  norm_cast
  simp

theorem leftMoves_intCast_zero_lt {a : ℤ} (h1 : 0 < a)
    : ((a - 1 : ℤ) : G) ∈ moves .left (a : G) := by
  simp [h1]

theorem leftMoves_intCast_zero_le_succ {a : ℤ} (h1 : 0 ≤ a)
    : ((a : ℤ) : G) ∈ moves .left (((a + 1) : ℤ) : G) := by
  have := leftMoves_intCast_zero_lt (G := G) (Int.le_iff_lt_add_one.mp h1)
  simp only [Int.add_sub_cancel] at this
  exact this

theorem leftMoves_intCast_le_zero_of_empty {k : ℤ} (h1 : 0 ≤ k) (h2 : moves .left (k : G) = ∅)
    : k = 0 := by
  obtain h_lt | h_eq := lt_or_eq_of_le h1
  · have h3 := leftMoves_intCast_zero_lt (G := G) h_lt
    simp [h2] at h3
  · exact h_eq.symm

theorem leftMoves_intCast_le_one_eq {a : ℤ} (h1 : 1 ≤ a)
    : moves .left ((a : ℤ) : G) = {((a - 1 : ℤ) : G)} := by
  obtain ⟨x, h2⟩ := Int.le.dest h1
  rw [<-h2, Int.add_comm 1 _]
  simp

@[simp]
theorem leftMoves_intCast_le_one_ne_empty {a : ℤ} (h1 : 1 ≤ a)
    : moves .left ((a : ℤ) : G) ≠ ∅ := by
  simp [leftMoves_intCast_le_one_eq h1]

@[simp]
theorem rightMoves_intCast {a : ℤ} (h1 : 0 ≤ a) : moves .right (a : G) = ∅ := by
  have h2 : 0 < a + 1 := by omega
  obtain ⟨x', h_x'⟩ := (CanLift.prf a h1 : ∃ (x' : ℕ), x' = a)
  rw [<-h_x', intCast_nat]
  simp only [rightMoves_natCast]

@[simp]
theorem leftMoves_intCast_le_zero_ne_empty {a : ℤ} (h1 : 0 ≤ a)
    : moves .left (((a + 1) : ℤ) : G) ≠ ∅ := by
  have h2 : 0 < a + 1 := by omega
  simp [h2]

@[simp, norm_cast]
protected theorem natCast_eq_zero_iff {n : ℕ} : (n : G) = 0 ↔ n = 0 := by
  constructor
  · cases n with
    | zero => simp only [Nat.cast_zero, imp_self]
    | succ n =>
      intro h
      exfalso
      have := moves_zero (G := G) .left
      simp [<-h] at this
  · intro h1
    simp only [h1, Nat.cast_zero]

@[simp]
theorem mem_moves_add_one_iff_mem_moves {g : G} {p : Player} {n : ℕ}
    : (g + 1 ∈ moves p (n + 1 : G)) ↔ (g ∈ moves p (n : G)) := by
  cases p
  · apply Iff.intro <;> intro h1
    · simp only [leftMoves_natCast_succ, Set.mem_singleton_iff] at h1
      simp [<-h1]
    · exact add_right_mem_moves_add h1 1
  · simp

@[simp]
theorem one_right_end : IsEnd .right (1 : G) := by
  simp only [IsEnd_def, rightMoves_one]

@[simp]
theorem natCast_IsEnd_right (n : ℕ) : IsEnd .right (n : G) := by
  induction n with
  | zero => simp only [Nat.cast_zero, IsEnd_zero]
  | succ k ih => simp only [IsEnd_def, Nat.cast_add, Nat.cast_one, moves_add, rightMoves_natCast,
                            Set.image_empty, rightMoves_one, Set.union_self]

@[simp]
theorem natCast_succ_not_IsEnd_left (n : ℕ) : ¬IsEnd .left (n.succ : G) := by
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, one_def,
             IsEnd.add_iff, not_and]
  intro _
  simp [IsEnd_def]

@[simp]
theorem ofSets_IsEndLike_iff {p : Player} {s t : Set G} [Small s] [Small t]
    : IsEndLike p !{s | t} ↔ IsEnd p !{s | t} := ofSets_IsEndLike_iff' p s t

theorem ofSets_add_ofSets
    (s₁ t₁ s₂ t₂ : Set G) [Small s₁] [Small t₁] [Small s₂] [Small t₂] :
    !{s₁ | t₁} + !{s₂ | t₂} =
      !{(· + !{s₂ | t₂}) '' s₁ ∪ (!{s₁ | t₁} + ·) '' s₂ |
        (· + !{s₂ | t₂}) '' t₁ ∪ (!{s₁ | t₁} + ·) '' t₂} := ofSets_add_ofSets'' s₁ t₁ s₂ t₂

theorem ofSets_add_ofSets' (st₁ st₂ : Player → Set G)
    [Small (st₁ .left)] [Small (st₂ .left)] [Small (st₁ .right)] [Small (st₂ .right)] :
    !{st₁} + !{st₂} =
      !{fun p ↦ (· + !{st₂}) '' st₁ p ∪ (!{st₁} + ·) '' st₂ p} := by
  rw [ofSets_eq_ofSets_cases, ofSets_eq_ofSets_cases st₂, ofSets_eq_ofSets_cases (fun _ ↦ _ ∪ _),
    ofSets_add_ofSets]

theorem natCast_add_one_ofSets {n : ℕ} : ((n + 1 : ℕ) : G) = !{{(n : G)} | ∅} := by
  induction n with
  | zero => simp [one_def]
  | succ k ih =>
    rw [Nat.cast_add, ih, natCast_one, one_def, ofSets_add_ofSets]
    simp only [Set.image_singleton, add_zero, Set.union_singleton, Set.image_empty, Set.union_self,
               ofSets_inj', Player.cases_inj, and_true]
    rw [<-one_def, <-natCast_one, <-Nat.cast_add, ih]
    simp only [Set.mem_singleton_iff, Set.insert_eq_of_mem]

@[simp]
theorem natCast_IsEndLike_iff {p : Player} {n : ℕ}
    : IsEndLike p (n : G) ↔ IsEnd p (n : G) := by
  match n with
  | 0 =>
    rw [natCast_zero]
    nth_rw 1 [zero_def]
    simp only [IsEnd_zero, iff_true]
    refine IsEnd.IsEndLike ?_
    rw [<-zero_def]
    exact IsEnd_zero
  | m + 1 =>
    rw [natCast_add_one_ofSets]
    simp

@[simp]
theorem IsEndLike_right_one : IsEndLike .right (1 : G) := by
  rw [<-natCast_one, natCast_IsEndLike_iff, natCast_one]
  exact one_right_end

@[simp]
theorem not_IsEndLike_left_one : ¬IsEndLike .left (1 : G) := by
  rw [<-natCast_one, natCast_IsEndLike_iff, natCast_one, one_def, IsEnd_def]
  simp only [moves_ofSets, Player.cases, Set.singleton_ne_empty, not_false_eq_true]

theorem natCast_ext {k m : ℕ}
    (h_moves : ∀ p, ∀ gp, gp ∈ moves p (k : G) ↔ gp ∈ moves p (m : G)) : (k : G) = (m : G) := by
  match k with
  | 0 =>
    match m with
    | 0 => rfl
    | y + 1 =>
      simp [natCast_add_one_ofSets, zero_def] at h_moves
  | x + 1 =>
    match m with
    | 0 => simp [natCast_add_one_ofSets, zero_def] at h_moves
    | y + 1 =>
      simp [natCast_add_one_ofSets] at h_moves
      simpa [natCast_add_one_ofSets]

@[simp]
theorem IsEnd_left_nat_zero {n : ℕ} : (IsEnd .left (n : G) ↔ n = 0) := by
  apply Iff.intro <;> intro h1
  · rw [<-Form.natCast_eq_zero_iff (G := G), <-natCast_zero]
    apply natCast_ext
    intro p gp
    apply Iff.intro <;> intro h2
    · cases p
      · simp [h1] at h2
      · simp at h2
    · simp at h2
  · simp [h1, IsEnd_def]

protected theorem natCast_injective : Function.Injective (@Nat.cast G _) := by
  intro a b h1
  induction a generalizing b with
  | zero =>
    norm_cast at h1
    exact (Form.natCast_eq_zero_iff.mp h1.symm).symm
  | succ k ih =>
    match b with
    | 0 =>
      norm_cast at h1
      exact Form.natCast_eq_zero_iff.mp h1
    | m + 1 =>
      simp only [Nat.cast_succ] at h1
      apply congr_arg Nat.succ
      apply ih
      apply natCast_ext
      intro p gp
      apply Iff.intro <;> intro h2
      · rwa [<-mem_moves_add_one_iff_mem_moves, <-h1, mem_moves_add_one_iff_mem_moves]
      · rwa [<-mem_moves_add_one_iff_mem_moves, h1, mem_moves_add_one_iff_mem_moves]

@[simp, norm_cast]
protected theorem natCast_injective' {n m : ℕ} : ((m : G) = (n : G)) ↔ m = n := by
  exact Function.Injective.eq_iff Form.natCast_injective

instance : CharZero G where
  cast_injective := Form.natCast_injective

theorem eq_sub_one_of_mem_leftMoves_intCast {n : ℤ} {x : G} (hx : x ∈ moves .left (n : G)) :
    x = (n - 1 : ℤ) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · cases n
    · simp [moves_zero] at hx
    · rw [intCast_nat] at hx
      simp_all
  · simp only [intCast_neg, intCast_nat, moves_neg, Player.neg_left,
               rightMoves_natCast, Set.neg_empty, Set.mem_empty_iff_false] at hx

theorem eq_add_one_of_mem_rightMoves_intCast {n : ℤ} {x : G} (hx : x ∈ moves .right (n : G)) :
    x = (n + 1 : ℤ) := by
  have : -x ∈ moves .left ((-n : ℤ) : G) := by simpa [moves_neg]
  rw [← neg_inj]
  simpa [← Form.intCast_neg, Int.neg_add] using eq_sub_one_of_mem_leftMoves_intCast this

/-- Every left option of an integer is equal to a smaller integer. -/
theorem eq_intCast_of_mem_leftMoves_intCast {n : ℤ} {x : G} (hx : x ∈ moves .left (n : G)) :
    ∃ m : ℤ, m < n ∧ m = x := by
  use n - 1
  simp [eq_sub_one_of_mem_leftMoves_intCast hx]
  omega -- really?

theorem eq_intCast_of_mem_rightMoves_intCast {n : ℤ} {x : G} (hx : x ∈ moves .right (n : G)) :
    ∃ m : ℤ, n < m ∧ m = x := by
  use n + 1
  simp [eq_add_one_of_mem_rightMoves_intCast hx]
  omega

theorem succ_nat_end_right {p : Player} {n : ℕ} : IsEnd p (n.succ : G) ↔ p = .right := by
  cases p <;> simp [IsEnd_def]

/-- If it holds for the previous natural, it holds for all moves of this natural as it is the only move -/
theorem nat_forall_moves {n : ℕ} {P : G → Prop} (h1 : P n)
    : ∀ (p : Player), ∀ gp ∈ moves p (n.succ : G), P gp := by
  intro p; cases p
  · intro gl h_mem
    rw [<-intCast_nat] at h_mem
    rw [eq_sub_one_of_mem_leftMoves_intCast h_mem, Nat.succ_eq_add_one]
    simpa
  · intro gr h_mem
    rw [Form.rightMoves_natCast] at h_mem
    exact False.elim h_mem

@[simp]
theorem add_eq_zero_iff {x y : G} : x + y = 0 ↔ x = 0 ∧ y = 0 := by
  exact add_eq_zero_iff' x y

instance : SubtractionCommMonoid G where
  neg_add_rev x y := by rw [neg_add', add_comm]
  neg_eq_of_add x y h1 := by simp_all only [add_eq_zero_iff, neg_zero]

end Form
