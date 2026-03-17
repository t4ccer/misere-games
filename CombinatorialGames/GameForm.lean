/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Reid Barton, Mario Carneiro, Isabel Longbottom, Kim Morrison, Yuyang Zhao
-/
module

public import CombinatorialGames.Mathlib.Small
public import CombinatorialGames.OfSets
public import CombinatorialGames.Form
public import Mathlib.Algebra.Group.Pointwise.Set.Small
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.QPF.Univariate.Basic
public import Mathlib.Logic.Small.Defs
public import Mathlib.Logic.Small.Set

universe u

open Form

@[expose] public noncomputable section

def GameFunctor (α : Type (u + 1)) : Type (u + 1) :=
  {s : Player → Set α // ∀ p, Small.{u} (s p)}

namespace GameFunctor

@[ext] theorem ext {α : Type (u + 1)} {x y : GameFunctor α} : x.1 = y.1 → x = y := Subtype.ext

instance {α : Type (u + 1)} (x : GameFunctor α) (p : Player) : Small.{u} (x.1 p) := x.2 p

instance : Functor GameFunctor where
  map f s := ⟨(f '' s.1 ·), fun _ => by infer_instance⟩

theorem map_def {α β} (f : α → β) (s : GameFunctor α) :
    f <$> s = ⟨(f '' s.1 ·), fun _ => by infer_instance⟩ :=
  rfl

instance : QPF GameFunctor where
  P := ⟨Player → Type u, fun x ↦ Σ p, PLift (x p)⟩
  abs x := ⟨fun p ↦ Set.range (x.2 ∘ .mk p ∘ PLift.up), fun _ ↦ by infer_instance⟩
  repr x := ⟨fun p ↦ Shrink (x.1 p), Sigma.rec (fun _ y ↦ ((equivShrink _).symm y.1).1)⟩
  abs_repr x := by
    cases x with | mk s hs =>
    apply Subtype.ext
    funext p; ext z; constructor
    · rintro ⟨y, rfl⟩; exact ((equivShrink ↑(s p)).symm y).2
    · intro hz
      exact ⟨equivShrink ↑(s p) ⟨z, hz⟩,
        congrArg Subtype.val ((equivShrink ↑(s p)).left_inv ⟨z, hz⟩)⟩
  abs_map f := by intro ⟨x, f⟩; ext; simp [PFunctor.map, map_def]

end GameFunctor

def GameForm : Type (u + 1) :=
  QPF.Fix GameFunctor

namespace GameForm

/-- Construct an `GameForm` from its left and right sets. -/
instance : OfSets GameForm fun _ ↦ True where
  ofSets (st : Player → Set GameForm) _ := QPF.Fix.mk ⟨st, fun
    | .left => (inferInstance : Small.{u} (st .left))
    | .right => (inferInstance : Small.{u} (st .right))⟩

/-- The set of moves of the game. -/
private def moves' (p : Player) (x : GameForm.{u}) : Set GameForm.{u} := x.dest.1 p

@[no_expose] instance : Moves GameForm where
  moves := moves'
  isOption'_wf := by
    refine ⟨fun x ↦ ?_⟩
    apply QPF.Fix.ind
    unfold Moves.IsOption' moves'
    rintro _ ⟨⟨st, hst⟩, rfl⟩
    constructor
    rintro y hy
    rw [QPF.Fix.dest_mk, Set.mem_iUnion] at hy
    obtain ⟨_, ⟨_, h⟩, _, rfl⟩ := hy
    exact h

/-- The set of left moves of the game. -/
scoped notation:max x:max "ᴸ" => moves Player.left x

/-- The set of right moves of the game. -/
scoped notation:max x:max "ᴿ" => moves Player.right x

instance instSmallElemMoves (p : Player) (x : GameForm.{u}) : Small.{u} (moves p x) := x.dest.2 p

@[simp]
theorem moves_ofSets (p) (st : Player → Set GameForm) [Small.{u} (st .left)] [Small.{u} (st .right)] :
    moves p !{st} = st p := by
  dsimp [ofSets]; ext; simp only [moves, moves', QPF.Fix.dest_mk]

@[simp]
theorem ofSets_moves (x : GameForm) : !{fun p => moves p x} = x := x.mk_dest

@[simp]
theorem leftMoves_ofSets (s t : Set GameForm) [Small.{u} s] [Small.{u} t] : !{s | t}ᴸ = s :=
  moves_ofSets ..

@[simp]
theorem rightMoves_ofSets (s t : Set GameForm) [Small.{u} s] [Small.{u} t] : !{s | t}ᴿ = t :=
  moves_ofSets ..

@[simp]
theorem ofSets_leftMoves_rightMoves (x : GameForm) : !{xᴸ | xᴿ} = x := by
  convert x.ofSets_moves with p
  cases p <;> rfl

/-- Two `GameForm`s are equal when their move sets are. -/
@[ext]
theorem ext {x y : GameForm.{u}} (h : ∀ p, moves p x = moves p y) :
    x = y := by
  rw [← ofSets_moves x, ← ofSets_moves y]
  simp_rw [funext h]

@[simp]
theorem ofSets_inj' {st₁ st₂ : Player → Set GameForm}
    [Small (st₁ .left)] [Small (st₁ .right)] [Small (st₂ .left)] [Small (st₂ .right)] :
    !{st₁} = !{st₂} ↔ st₁ = st₂ := by
  simp_rw [GameForm.ext_iff, moves_ofSets, funext_iff]

theorem ofSets_inj {s₁ s₂ t₁ t₂ : Set GameForm} [Small s₁] [Small s₂] [Small t₁] [Small t₂] :
    !{s₁ | t₁} = !{s₂ | t₂} ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp

instance (x : GameForm.{u}) : Small.{u} {y // IsOption y x} :=
  inferInstanceAs (Small (⋃ p, moves p x))

instance (x : GameForm.{u}) : Small.{u} {y // Subposition y x} :=
  small_transGen' _ x

-- We make no use of `GameForm`'s definition from a `QPF` after this point.
attribute [irreducible] GameForm

/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets. You rarely need to use this explicitly, as the termination checker will handle
things for you.

See `ofSetsRecOn` for an alternate form. -/
@[elab_as_elim]
def moveRecOn {motive : GameForm → Sort*} (x)
    (mk : Π x, (Π p, Π y ∈ moves p x, motive y) → motive x) : motive x :=
  mk x (fun p y _ ↦ moveRecOn y mk)
termination_by x
decreasing_by form_wf

theorem moveRecOn_eq {motive : GameForm → Sort*} (x)
    (mk : Π x, (Π p, Π y ∈ moves p x, motive y) → motive x) :
    moveRecOn x mk = mk x (fun _ y _ ↦ moveRecOn y mk) := by
  rw [moveRecOn]

/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets. You rarely need to use this explicitly, as the termination checker will handle
things for you.

See `moveRecOn` for an alternate form. -/
@[elab_as_elim]
def ofSetsRecOn {motive : GameForm.{u} → Sort*} (x)
    (mk : Π (s t : Set GameForm) [Small s] [Small t],
      (Π x ∈ s, motive x) → (Π x ∈ t, motive x) → motive !{s | t}) :
    motive x :=
  cast (by simp) <| moveRecOn (motive := fun x ↦ motive !{xᴸ | xᴿ}) x
    fun x IH ↦ mk _ _
      (fun y hy ↦ cast (by simp) (IH .left y hy)) (fun y hy ↦ cast (by simp) (IH .right y hy))

@[simp]
theorem ofSetsRecOn_ofSets {motive : GameForm.{u} → Sort*}
    (s t : Set GameForm) [Small.{u} s] [Small.{u} t]
    (mk : Π (s t : Set GameForm) [Small s] [Small t],
      (Π x ∈ s, motive x) → (Π x ∈ t, motive x) → motive !{s | t}) :
    ofSetsRecOn !{s | t} mk = mk _ _ (fun y _ ↦ ofSetsRecOn y mk) (fun y _ ↦ ofSetsRecOn y mk) := by
  rw [ofSetsRecOn, cast_eq_iff_heq, moveRecOn_eq]
  congr
  any_goals simp
  all_goals
    refine Function.hfunext rfl fun x _ h ↦ ?_
    cases h
    refine Function.hfunext ?_ fun _ _ _ ↦ ?_
    · simp
    · rw [ofSetsRecOn, cast_heq_iff_heq, heq_cast_iff_heq]

/-! ### Basic games -/

/-- The game `0 = !{∅ | ∅}`. -/
instance : Zero GameForm := ⟨!{fun _ ↦ ∅}⟩

theorem zero_def : (0 : GameForm) = !{fun _ ↦ ∅} := rfl

private theorem moves_zero' (p : Player) : moves p (0 : GameForm) = ∅ := moves_ofSets ..

instance : Inhabited GameForm := ⟨0⟩

/-- The game `1 = !{{0} | ∅}`. -/
instance : One GameForm := ⟨!{{0} | ∅}⟩

theorem one_def : (1 : GameForm) = !{{0} | ∅} := rfl

@[simp] theorem leftMoves_one : (1 : GameForm)ᴸ = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_one : (1 : GameForm)ᴿ = ∅ := rightMoves_ofSets ..

/-! ### Negation -/

private def neg' (x : GameForm) : GameForm :=
  !{Set.range fun y : xᴿ ↦ neg' y.1 | Set.range fun y : xᴸ ↦ neg' y.1}
termination_by x
decreasing_by form_wf

/-- The negative of a game is defined by `-!{s | t} = !{-t | -s}`. -/
@[no_expose] instance : Neg GameForm where
  neg := neg'

private theorem neg_ofSets'' (s t : Set GameForm) [Small s] [Small t] :
    -!{s | t} = !{Neg.neg '' t | Neg.neg '' s} := by
  change neg' _ = _
  rw [neg']
  simp [Neg.neg, Set.ext_iff]

instance : InvolutiveNeg GameForm where
  neg_neg x := by
    refine ofSetsRecOn x ?_
    aesop (add simp [neg_ofSets''])

@[simp]
theorem neg_ofSets (s t : Set GameForm) [Small s] [Small t] : -!{s | t} = !{-t | -s} := by
  simp_rw [neg_ofSets'', Set.image_neg_eq_neg]

theorem neg_ofSets' (st : Player → Set GameForm) [Small (st .left)] [Small (st .right)] :
    -!{st} = !{fun p ↦ -st (-p)} := by
  rw [ofSets_eq_ofSets_cases, ofSets_eq_ofSets_cases fun _ ↦ -_, neg_ofSets]
  rfl

@[simp]
theorem neg_ofSets_const (s : Set GameForm) [Small s] :
    -!{fun _ ↦ s} = !{fun _ ↦ -s} := by
  simp [neg_ofSets']

instance : NegZeroClass GameForm where
  neg_zero := by simp [zero_def]

theorem neg_eq (x : GameForm) : -x = !{-xᴿ | -xᴸ} := by
  rw [← neg_ofSets, ofSets_leftMoves_rightMoves]

theorem neg_eq' (x : GameForm) : -x = !{fun p ↦ -moves (-p) x} := by
  rw [neg_eq, ofSets_eq_ofSets_cases (fun _ ↦ -_)]; rfl

private theorem moves_neg' (p : Player) (x : GameForm) :
    moves p (-x) = -moves (-p) x := by
  rw [neg_eq', moves_ofSets]

/-! ### Addition and subtraction -/

set_option maxHeartbeats 400000 in
private def add' (x y : GameForm) : GameForm :=
  !{(Set.range fun z : moves .left x ↦ add' z y) ∪ (Set.range fun z : moves .left y ↦ add' x z) |
    (Set.range fun z : moves .right x ↦ add' z y) ∪ (Set.range fun z : moves .right y ↦ add' x z)}
termination_by (x, y)
decreasing_by form_wf

/-- The sum of `x = !{s₁ | t₁}` and `y = !{s₂ | t₂}` is `!{s₁ + y, x + s₂ | t₁ + y, x + t₂}`. -/
@[no_expose] instance : Add GameForm where
  add := add'

theorem add_eq (x y : GameForm) : x + y =
    !{(· + y) '' xᴸ ∪ (x + ·) '' yᴸ | (· + y) '' xᴿ ∪ (x + ·) '' yᴿ} := by
  change add' _ _ = _
  rw [add']
  simp [HAdd.hAdd, Add.add, Set.ext_iff]

theorem add_eq' (x y : GameForm) : x + y =
    !{fun p ↦ (· + y) '' moves p x ∪ (x + ·) '' moves p y} := by
  rw [add_eq, ofSets_eq_ofSets_cases (fun _ ↦ _ ∪ _)]

theorem ofSets_add_ofSets
    (s₁ t₁ s₂ t₂ : Set GameForm) [Small s₁] [Small t₁] [Small s₂] [Small t₂] :
    !{s₁ | t₁} + !{s₂ | t₂} =
      !{(· + !{s₂ | t₂}) '' s₁ ∪ (!{s₁ | t₁} + ·) '' s₂ |
        (· + !{s₂ | t₂}) '' t₁ ∪ (!{s₁ | t₁} + ·) '' t₂} := by
  rw [add_eq]
  simp

theorem ofSets_add_ofSets' (st₁ st₂ : Player → Set GameForm)
    [Small (st₁ .left)] [Small (st₂ .left)] [Small (st₁ .right)] [Small (st₂ .right)] :
    !{st₁} + !{st₂} =
      !{fun p ↦ (· + !{st₂}) '' st₁ p ∪ (!{st₁} + ·) '' st₂ p} := by
  rw [ofSets_eq_ofSets_cases, ofSets_eq_ofSets_cases st₂, ofSets_eq_ofSets_cases (fun _ ↦ _ ∪ _),
    ofSets_add_ofSets]

private theorem moves_add' (p : Player) (x y : GameForm) :
    moves p (x + y) = (· + y) '' moves p x ∪ (x + ·) '' moves p y := by
  rw [add_eq', moves_ofSets]

theorem isOption_neg {x y : GameForm} : IsOption x (-y) ↔ IsOption (-x) y := by
  simp only [moves_neg', IsOption.iff_mem_union, Player.neg_left, Player.neg_right,
             Set.union_comm, Set.mem_union, Set.mem_neg]

@[simp]
theorem isOption_neg_neg {x y : GameForm} : IsOption (-x) (-y) ↔ IsOption x y := by
  rw [isOption_neg, neg_neg]

theorem forall_moves_neg {P : GameForm → Prop} {p : Player} {x : GameForm} :
    (∀ y ∈ moves p (-x), P y) ↔ (∀ y ∈ moves (-p) x, P (-y)) := by
  simp only [moves_neg', Set.mem_neg, Set.forall_neg_mem]

theorem IsOption.add_left {x y z : GameForm} (h : IsOption x y) : IsOption (z + x) (z + y) := by
  aesop (add simp [moves_add'])

theorem IsOption.add_right {x y z : GameForm} (h : IsOption x y) : IsOption (x + z) (y + z) := by
  aesop (add simp [moves_add'])

theorem forall_moves_add {p : Player} {P : GameForm → Prop} {x y : GameForm} :
    (∀ a ∈ moves p (x + y), P a) ↔
      (∀ a ∈ moves p x, P (a + y)) ∧ (∀ b ∈ moves p y, P (x + b)) := by
  aesop (add simp [moves_add'])

@[simp]
theorem add_eq_zero_iff {x y : GameForm} : x + y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor <;> simp_all [GameForm.ext_iff, moves_add', moves_zero']

private theorem add_zero' (x : GameForm) : x + 0 = x := by
  refine moveRecOn x ?_
  aesop (add simp [moves_zero', moves_add'])

private theorem add_comm' (x y : GameForm) : x + y = y + x := by
  ext
  simp only [moves_add', Set.mem_union, Set.mem_image, or_comm]
  congr! 3 <;>
  · refine and_congr_right_iff.2 fun h ↦ ?_
    rw [add_comm']
termination_by (x, y)
decreasing_by form_wf

private theorem add_assoc' (x y z : GameForm) : x + y + z = x + (y + z) := by
  ext1
  simp only [moves_add', Set.image_union, Set.image_image, Set.union_assoc]
  refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_) <;>
  · ext
    congr! 2
    rw [add_assoc']
termination_by (x, y, z)
decreasing_by form_wf

instance : AddCommMonoid GameForm where
  add_zero := private add_zero'
  zero_add _ := private add_comm' .. ▸ add_zero' _
  add_comm := private add_comm'
  add_assoc := private add_assoc'
  nsmul := nsmulRec

/-- The subtraction of `x` and `y` is defined as `x + (-y)`. -/
instance : SubNegMonoid GameForm where
  zsmul := zsmulRec

/-- We define the `NatCast` instance as `↑0 = 0` and `↑(n + 1) = !{{↑n} | ∅}`. -/
instance : AddCommMonoidWithOne GameForm where

@[simp]
theorem moves_sub (p : Player) (x y : GameForm) :
    moves p (x - y) = (· - y) '' moves p x ∪ (x + ·) '' (-moves (-p) y) := by
  simp only [sub_eq_add_neg, moves_add', moves_neg']

private theorem neg_add' (x y : GameForm) : -(x + y) = -x + -y := by
  ext
  simp only [moves_neg', moves_add', Set.union_neg, Set.mem_union, Set.mem_neg, Set.mem_image,
             Set.exists_neg_mem]
  congr! 3 <;>
  · refine and_congr_right_iff.2 fun _ ↦ ?_
    rw [← neg_inj, neg_add', neg_neg]
termination_by (x, y)
decreasing_by form_wf

instance : SubtractionCommMonoid GameForm where
  neg_neg := neg_neg
  neg_add_rev x y := by rw [neg_add', add_comm]
  neg_eq_of_add := by simp only [add_eq_zero_iff, and_imp, forall_eq_apply_imp_iff, forall_eq, neg_zero]
  add_comm := add_comm

instance : Form GameForm where
  moves_neg' := private moves_neg'
  moves_add' := private moves_add'
  moves_zero' := private moves_zero'
  moves_small' := instSmallElemMoves
  IsEndLike p x := moves p x = ∅
  IsEndLike_ofEnd' _ _ h1 := h1
  IsEndLike_add_iff' p x y := by simp [moves_add']
  IsEndLike_neg_iff_neg' p g := by
    constructor <;> cases p
    all_goals
    · intro h1
      simp only [moves_neg', Player.neg_left, Player.neg_right, Set.neg_eq_empty] at h1 ⊢
      exact h1

@[simp]
theorem IsEndLike_iff {g : GameForm} {p : Player} : IsEndLike p g ↔ IsEnd p g := by
  simp only [IsEndLike, IsEnd_def]

/-- This version of the theorem is more convenient for the `game_cmp` tactic. -/
theorem leftMoves_natCast_succ' : ∀ n : ℕ, (n.succ : GameForm)ᴸ = {(n : GameForm)}
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_succ, moves_add, leftMoves_natCast_succ']
    simp

@[simp 1100] -- This should trigger before `leftMoves_add`.
theorem leftMoves_natCast_succ (n : ℕ) : ((n + 1) : GameForm)ᴸ = {(n : GameForm)} :=
  leftMoves_natCast_succ' n

@[simp 1100] -- This should trigger before `rightMoves_add`.
theorem rightMoves_natCast : ∀ n : ℕ, (n : GameForm)ᴿ = ∅
  | 0 => by simp [moves_zero]
  | n + 1 => by
    rw [Nat.cast_succ, moves_add, rightMoves_natCast]
    simp

@[simp 1100]
theorem leftMoves_ofNat (n : ℕ) [n.AtLeastTwo] : ofNat(n)ᴸ = {((n - 1 : ℕ) : GameForm)} := by
  change (n : GameForm)ᴸ = _
  rw [← Nat.succ_pred (NeZero.out (n := n)), leftMoves_natCast_succ']
  simp

@[simp 1100]
theorem rightMoves_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : GameForm)ᴿ = ∅ :=
  rightMoves_natCast n

@[simp]
theorem not_mem_right_nat (gr : GameForm) (n : ℕ) : ¬(gr ∈ moves Player.right (n : GameForm)) := by
  simp only [GameForm.rightMoves_natCast, Set.mem_empty_iff_false, not_false_eq_true]

theorem natCast_succ_eq (n : ℕ) : (n + 1 : GameForm) = !{{(n : GameForm)} | ∅} := by
  ext p; cases p <;> simp [moves_add]

/-- Every left option of a natural number is equal to a smaller natural number. -/
theorem eq_natCast_of_mem_leftMoves_natCast {n : ℕ} {x : GameForm} (hx : x ∈ (n : GameForm)ᴸ) :
    ∃ m : ℕ, m < n ∧ m = x := by
  cases n with
  | zero => simp [moves_zero] at hx
  | succ n =>
    use n
    simp_all

instance : IntCast GameForm where
  intCast
  | .ofNat n => n
  | .negSucc n => -(n + 1)

@[simp, norm_cast] theorem intCast_nat (n : ℕ) : ((n : ℤ) : GameForm) = n := rfl
@[simp] theorem intCast_ofNat (n : ℕ) : ((ofNat(n) : ℤ) : GameForm) = n := rfl
@[simp] theorem intCast_negSucc (n : ℕ) : (Int.negSucc n : GameForm) = -(n + 1) := rfl

@[norm_cast] theorem intCast_zero : ((0 : ℤ) : GameForm) = 0 := rfl
@[norm_cast] theorem intCast_one : ((1 : ℤ) : GameForm) = 1 := by simp

@[norm_cast] theorem natCast_zero : ((0 : ℕ) : GameForm) = 0 := rfl
@[norm_cast] theorem natCast_one : ((1 : ℕ) : GameForm) = 1 := by simp

@[simp, norm_cast]
theorem intCast_neg (n : ℤ) : ((-n : ℤ) : GameForm) = -(n : GameForm) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero => simp
    | succ n => rfl
  | negSucc n => exact (neg_neg _).symm

@[simp]
theorem leftMoves_eq_natCast_zero_lt {a : ℕ} (h1 : 0 < a)
    : moves .left (a : GameForm) = {((a - 1 : ℕ) : GameForm)} := by
  obtain ⟨x, h2⟩ := Nat.exists_add_one_eq.mpr h1
  rw [<-h2]
  simp

theorem leftMoves_natCast_zero_lt {a : ℕ} (h1 : 0 < a)
    : ((a - 1 : ℕ) : GameForm) ∈ moves .left (a : GameForm) := by
  simp [h1]

@[simp 1100] -- This should trigger before `leftMoves_add`.
theorem leftMoves_intCast_succ {n : ℤ} (h1 : 0 ≤ n) : ((n + 1) : GameForm)ᴸ = {(n : GameForm)} := by
  match n with
  | Int.ofNat n => simp
  | Int.negSucc k => simp

@[simp]
theorem leftMoves_intCast {a : ℤ} (h1 : 0 < a)
    : moves .left (a : GameForm) = {((a - 1 : ℤ) : GameForm)} := by
  have : ∃ x, x + 1 = a := by use a - 1; simp
  obtain ⟨x, h2⟩ := this
  rw [<-h2]
  have h3 : 0 ≤ x := by omega
  have := leftMoves_intCast_succ h3
  rw [add_sub_cancel_right, <-this]
  congr
  have natCast_add_one {a : ℕ} : (((a + 1) : ℕ) : GameForm) = a + 1 := ext (congrFun rfl)
  obtain ⟨x', h_x'⟩ := (CanLift.prf x h3 : ∃ (x' : ℕ), x' = x)
  nth_rewrite 2 [<-h_x']
  rw [intCast_nat, <-natCast_add_one, <-intCast_nat]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [h_x']

theorem leftMoves_intCast_zero_lt {a : ℤ} (h1 : 0 < a)
    : ((a - 1 : ℤ) : GameForm) ∈ moves .left (a : GameForm) := by
  simp [h1]

theorem leftMoves_intCast_zero_le_succ {a : ℤ} (h1 : 0 ≤ a)
    : ((a : ℤ) : GameForm) ∈ moves .left (((a + 1) : ℤ) : GameForm) := by
  have := leftMoves_intCast_zero_lt (Int.le_iff_lt_add_one.mp h1)
  rwa [add_sub_cancel_right] at this

theorem leftMoves_intCast_le_zero_of_empty {k : ℤ} (h1 : 0 ≤ k) (h2 : moves .left (k : GameForm) = ∅)
    : k = 0 := by
  obtain h_lt | h_eq := lt_or_eq_of_le h1
  · have h3 := leftMoves_intCast_zero_lt h_lt
    rw [h2] at h3
    exact not_neZero.mp fun a ↦ h3
  · exact h_eq.symm

theorem leftMoves_intCast_le_one_eq {a : ℤ} (h1 : 1 ≤ a)
    : moves .left ((a : ℤ) : GameForm) = {((a - 1 : ℤ) : GameForm)} := by
  obtain ⟨x, h2⟩ := Int.le.dest h1
  rw [<-h2, add_comm]
  simp

@[simp]
theorem leftMoves_intCast_le_one_ne_empty {a : ℤ} (h1 : 1 ≤ a)
    : moves .left ((a : ℤ) : GameForm) ≠ ∅ := by
  simp [leftMoves_intCast_le_one_eq h1]

@[simp]
theorem rightMoves_intCast {a : ℤ} (h1 : 0 ≤ a) : moves .right (a : GameForm) = ∅ := by
  have h2 : 0 < a + 1 := by omega
  obtain ⟨x', h_x'⟩ := (CanLift.prf a h1 : ∃ (x' : ℕ), x' = a)
  rw [<-h_x', GameForm.intCast_nat]
  simp only [rightMoves_natCast]

@[simp]
theorem leftMoves_intCast_le_zero_ne_empty {a : ℤ} (h1 : 0 ≤ a)
    : moves .left (((a + 1) : ℤ) : GameForm) ≠ ∅ := by
  have h2 : 0 < a + 1 := by omega
  simp [h2]

@[simp, norm_cast]
protected theorem natCast_eq_zero_iff {n : ℕ} : (n : GameForm) = 0 ↔ n = 0 := by
  constructor
  · cases n with
    | zero => simp only [Nat.cast_zero, imp_self]
    | succ n =>
      intro h
      exfalso
      have h1 := GameForm.ext_iff.mp h .left
      rw [Nat.cast_add, Nat.cast_one, leftMoves_natCast_succ, moves_zero (G := GameForm)] at h1
      exact Set.singleton_ne_empty _ h1
  · intro h1
    simp only [h1, Nat.cast_zero]

@[simp]
theorem mem_moves_add_one_iff_mem_moves {g : GameForm} {p : Player} {n : ℕ}
    : (g + 1 ∈ moves p (n + 1 : GameForm)) ↔ (g ∈ moves p (n : GameForm)) := by
  cases p
  · apply Iff.intro <;> intro h1
    · simp only [leftMoves_natCast_succ, Set.mem_singleton_iff] at h1
      rw [<-h1]
      simp
    · exact add_right_mem_moves_add h1 1
  · simp

protected theorem natCast_injective : Function.Injective (@Nat.cast GameForm _) := by
  intro a b h1
  induction a generalizing b with
  | zero => exact (GameForm.natCast_eq_zero_iff.mp h1.symm).symm
  | succ k ih =>
    match b with
    | 0 => exact GameForm.natCast_eq_zero_iff.mp h1
    | m + 1 =>
      simp only [Nat.cast_succ] at h1
      apply congr_arg Nat.succ
      apply ih
      ext p gp
      apply Iff.intro <;> intro h2
      · rwa [<-mem_moves_add_one_iff_mem_moves, <-h1, mem_moves_add_one_iff_mem_moves]
      · rwa [<-mem_moves_add_one_iff_mem_moves, h1, mem_moves_add_one_iff_mem_moves]

@[simp, norm_cast]
protected theorem natCast_injective' {n m : ℕ} : ((m : GameForm) = (n : GameForm)) ↔ m = n := by
  exact Function.Injective.eq_iff GameForm.natCast_injective

instance : CharZero GameForm where
  cast_injective := GameForm.natCast_injective

theorem eq_sub_one_of_mem_leftMoves_intCast {n : ℤ} {x : GameForm} (hx : x ∈ (n : GameForm)ᴸ) :
    x = (n - 1 : ℤ) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · cases n
    · simp [moves_zero] at hx
    · rw [intCast_nat] at hx
      simp_all
  · simp only [intCast_neg, intCast_nat, moves_neg, Player.neg_left,
               rightMoves_natCast, Set.neg_empty, Set.mem_empty_iff_false] at hx

theorem eq_add_one_of_mem_rightMoves_intCast {n : ℤ} {x : GameForm} (hx : x ∈ (n : GameForm)ᴿ) :
    x = (n + 1 : ℤ) := by
  have : -x ∈ ((-n : ℤ) : GameForm)ᴸ := by simpa [moves_neg]
  rw [← neg_inj]
  simpa [← GameForm.intCast_neg, add_comm] using eq_sub_one_of_mem_leftMoves_intCast this

/-- Every left option of an integer is equal to a smaller integer. -/
theorem eq_intCast_of_mem_leftMoves_intCast {n : ℤ} {x : GameForm} (hx : x ∈ (n : GameForm)ᴸ) :
    ∃ m : ℤ, m < n ∧ m = x := by
  use n - 1
  simp [eq_sub_one_of_mem_leftMoves_intCast hx]

/-- Every right option of an integer is equal to a larger integer. -/
theorem eq_intCast_of_mem_rightMoves_intCast {n : ℤ} {x : GameForm} (hx : x ∈ (n : GameForm)ᴿ) :
    ∃ m : ℤ, n < m ∧ m = x := by
  use n + 1
  simp [eq_add_one_of_mem_rightMoves_intCast hx]

theorem leftEnd_rightEnd_eq_zero {g : GameForm} (h1 : IsEnd .left g) (h2 : IsEnd .right g) :
    g = 0 := by
  rw [IsEnd_def] at h1 h2
  rw [zero_def]
  ext p
  cases p
  · simp only [moves_ofSets, Set.mem_empty_iff_false, iff_false] at ⊢ h1
    simp only [h1, Set.mem_empty_iff_false, not_false_eq_true]
  · simp only [moves_ofSets] at ⊢ h2
    rw [h2]

theorem both_ends_eq_zero {g : GameForm} {p : Player} (h1 : IsEnd p g) (h2 : IsEnd (-p) g) :
    g = 0 := by
  cases p
  · exact leftEnd_rightEnd_eq_zero h1 h2
  · exact leftEnd_rightEnd_eq_zero h2 h1

theorem ne_zero_not_end {g : GameForm} (h1 : g ≠ 0) : ∃ p, ¬IsEnd p g := by
  apply not_forall.mp
  intro h2
  exact h1 (leftEnd_rightEnd_eq_zero (h2 .left) (h2 .right))

theorem succ_nat_end_right {p : Player} {n : ℕ} : IsEnd p (n.succ : GameForm) ↔ p = .right := by
  cases p <;> simp [IsEnd_def]

@[simp]
theorem zero_end {p : Player} : IsEnd p (0 : GameForm) := by
  simp only [IsEnd_def, zero_def, moves_ofSets]

@[simp]
theorem zero_not_both_end {g : GameForm} {p : Player} (h1 : g ≠ 0) (h2 : IsEnd p g) :
    ¬IsEnd (-p) g :=
  fun h3 => h1 (both_ends_eq_zero h2 h3)

@[simp]
theorem one_right_end : IsEnd .right (1 : GameForm) := by
  simp only [IsEnd_def, rightMoves_one]

@[simp]
theorem nat_IsEnd_right (n : ℕ) : IsEnd .right (n : GameForm) := by
  induction n with
  | zero => simp only [Nat.cast_zero, IsEnd_zero]
  | succ k ih => simp only [IsEnd_def, Nat.cast_add, Nat.cast_one, moves_add, rightMoves_natCast,
                            Set.image_empty, rightMoves_one, Set.union_self]

@[simp]
theorem IsEnd_left_nat_zero {n : ℕ} : (IsEnd .left (n : GameForm) ↔ n = 0) := by
  apply Iff.intro <;> intro h1
  · exact GameForm.natCast_eq_zero_iff.mp (both_ends_eq_zero h1 (nat_IsEnd_right n))
  · simp [h1, IsEnd_def]

/-- If it holds for the previous natural, it holds for all moves of this natural as it is the only move -/
theorem nat_forall_moves {n : ℕ} {P : GameForm → Prop} (h1 : P n)
    : ∀ (p : Player), ∀ gp ∈ moves p (n.succ : GameForm), P gp := by
  intro p; cases p
  · intro gl h_mem
    rw [<-intCast_nat] at h_mem
    rwa [eq_sub_one_of_mem_leftMoves_intCast h_mem, Nat.succ_eq_add_one, Nat.cast_add,
         Nat.cast_one, add_sub_cancel_right, GameForm.intCast_nat]
  · intro gr h_mem
    by_contra
    exact GameForm.not_mem_right_nat gr n.succ h_mem

end GameForm
