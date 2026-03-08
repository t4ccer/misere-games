/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Outcome
public import CombinatorialGames.GameForm.Birthday
public import CombinatorialGames.Form.Short
public import CombinatorialGames.Form.Misere.Outcome

public noncomputable section

namespace GameForm.Misere.Outcome

open Form
open Form.Misere.Outcome
open MisereForm

universe u

private def WinsGoingFirst' (p : Player) (g : GameForm) : Prop :=
  Form.IsEnd p g ∨ (∃ g', ∃ (_ : g' ∈ Form.moves p g), ¬WinsGoingFirst' (-p) g')
termination_by g
decreasing_by form_wf

private theorem End_WinsGoingFirst' {g : GameForm} {p : Player} (h1 : IsEnd p g)
    : WinsGoingFirst' p g := by
  rw [WinsGoingFirst']
  exact Or.inl h1

private theorem WinsGoingFirst_neg_iff' (g : GameForm) (p : Player) :
    (WinsGoingFirst' p (-g)) ↔ (WinsGoingFirst' (-p) g) := by
  constructor
    <;> intro h1
    <;> rw [WinsGoingFirst'] at h1
    <;> apply Or.elim h1
    <;> intro h1
  · exact End_WinsGoingFirst' (IsEnd_neg_iff_neg.mp h1)
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [WinsGoingFirst', neg_neg]
    simp only [exists_prop]
    apply Or.inr
    use -gp
    simp only [Form.moves_neg, Set.mem_neg] at h1
    exact And.intro h1 ((WinsGoingFirst_neg_iff' gp p).not.mpr h2)
  · exact End_WinsGoingFirst' (IsEnd_neg_iff_neg.mpr h1)
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [WinsGoingFirst']
    apply Or.inr
    use -gp
    simp only [Form.moves_neg, Set.mem_neg, neg_neg, exists_prop]
    apply And.intro h1
    have h3 := (WinsGoingFirst_neg_iff' (-gp) p).not.mp
    rw [neg_neg] at h2 h3
    exact h3 h2
termination_by Form.birthday g
decreasing_by all_goals gameform_birthday

@[no_expose] instance : MisereForm GameForm where
  WinsGoingFirst := WinsGoingFirst'
  WinsGoingFirst_neg_iff' := WinsGoingFirst_neg_iff'
  WinsGoingFirst_of_IsEnd' _ _ := End_WinsGoingFirst'

private theorem WinsGoingFirst_def (g : GameForm) (p : Player)
  : WinsGoingFirst p g ↔ WinsGoingFirst' p g := by rfl

theorem WinsGoingFirst_iff (g : GameForm) (p : Player)
    : WinsGoingFirst p g ↔ IsEnd p g ∨ (∃ g' ∈ moves p g, ¬WinsGoingFirst (-p) g') := by
  nth_rw 1 [MisereForm.WinsGoingFirst, instMisereForm]
  dsimp only [instForm.eq_1]
  unfold WinsGoingFirst'
  simp only [exists_prop, <-WinsGoingFirst_def]

theorem WinsGoingFirst_of_End {g : GameForm} {p : Player} (h1 : IsEnd p g)
    : WinsGoingFirst p g := End_WinsGoingFirst' h1

theorem WinsGoingFirst_of_moves {g : GameForm} {p : Player}
    (h1 : ∃ g' ∈ moves p g, ¬WinsGoingFirst (-p) g')
    : WinsGoingFirst p g := by
  simp only [WinsGoingFirst]
  unfold WinsGoingFirst'
  apply Or.inr
  exact bex_def.mpr h1

theorem not_WinsGoingFirst {g : GameForm} {p : Player}
    : ¬MisereForm.WinsGoingFirst p g ↔ (¬IsEnd p g ∧ (∀ g' ∈ moves p g, MisereForm.WinsGoingFirst (-p) g')) := by
  rw [WinsGoingFirst_iff]
  simp only [not_or, not_exists, not_and, not_not]

@[expose] def MisereEq (A : GameForm → Prop) (g h : GameForm) : Prop :=
  ∀ (x : GameForm), A x → MisereOutcome (g + x) = MisereOutcome (h + x)

macro x:term:51 " =m " u:term:max y:term:51 : term => `(MisereEq $u $x $y)

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab MisereEq]
meta def delabMisereEq : Delab := do
  let y ← withAppArg delab
  let x ← withAppFn do withAppArg delab
  let u ← withAppFn do withAppFn do withAppArg delab
  `($x =m $u $y)

theorem MisereEq_symm {A : GameForm → Prop} {g h : GameForm} (h1 : g =m A h) : h =m A g := by
  intro x h2
  have h3 := h1 x h2
  exact Eq.symm h3

theorem MisereEq_trans {A : GameForm → Prop} {g h k : GameForm} (h1 : g =m A h) (h2 : h =m A k) :
    g =m A k := by
  unfold MisereEq at *
  intro x h3
  exact cast (congrArg (Eq (MisereOutcome (g + x))) (h2 x h3)) (h1 x h3)

@[expose] def MisereGe (A : GameForm → Prop) (g h : GameForm) : Prop :=
  ∀ x, (A x → MisereOutcome (g + x) ≥ MisereOutcome (h + x))

/-- `G ≥m A H` means that G ≥_A H -/
macro x:term:51 " ≥m " u:term:max y:term:51 : term => `(MisereGe $u $x $y)

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab MisereGe]
meta def delabMisereGe : Delab := do
  let y ← withAppArg delab
  let x ← withAppFn do withAppArg delab
  let u ← withAppFn do withAppFn do withAppArg delab
  `($x ≥m $u $y)

theorem MisereGe_antisymm {A : GameForm → Prop} {g h : GameForm} (h1 : g ≥m A h) (h2 : h ≥m A g) :
    g =m A h := fun x h3 =>
  PartialOrder.le_antisymm (MisereOutcome (g + x)) (MisereOutcome (h + x)) (h2 x h3) (h1 x h3)

theorem MisereGe_trans {A : GameForm → Prop} {g h k : GameForm} (h1 : g ≥m A h) (h2 : h ≥m A k) :
    g ≥m A k := by
  unfold MisereGe at *
  intro x h3
  exact le_trans (h2 x h3) (h1 x h3)

theorem MisereGe_rw_left {A : GameForm → Prop} {a b c : GameForm} (h2 : b =m A c) (h1 : b ≥m A a) : c ≥m A a := by
  unfold MisereGe at h1 ⊢
  unfold MisereEq at h2
  intro x hx
  rw [<-h2 x hx]
  exact h1 x hx

theorem MisereGe_rw_right {A : GameForm → Prop} {a b c : GameForm} (h2 : b =m A c) (h1 : a ≥m A c) : a ≥m A b := by
  unfold MisereGe at h1 ⊢
  unfold MisereEq at h2
  intro x hx
  rw [h2 x hx]
  exact h1 x hx

theorem MisereGe_of_subset (U : GameForm → Prop) {V : GameForm → Prop}
    (h_v_subset_u : ∀g, V g → U g) (g h : GameForm) (h2 : g ≥m U h) : g ≥m V h := by
  unfold MisereGe at h2 ⊢
  intro x hv
  exact h2 x (h_v_subset_u x hv)

@[simp]
theorem MisereGe_refl {A : GameForm → Prop} (g : GameForm) : g ≥m A g := by
  unfold MisereGe
  intro x h3
  exact le_refl MisereOutcome (g + x)

theorem not_MisereEq_of_not_MisereGe {A : GameForm → Prop} {g h : GameForm} (h1 : ¬(g ≥m A h)) :
    ¬(g =m A h) := by
  simp only [MisereGe, ge_iff_le, not_forall] at h1
  obtain ⟨x, ⟨h1, h2⟩⟩ := h1
  simp only [MisereEq, not_forall]
  use x
  use h1
  exact Ne.symm (ne_of_not_le h2)

class ClosedUnderNeg (A : GameForm → Prop) where
  neg_of (g : GameForm) (h1 : A g) : A (-g)

instance : ClosedUnderNeg Form.Short where
  neg_of _ h := Form.Short.neg_iff.mpr h

private theorem ClosedUnderNeg.not_ge_neg_iff.aux {A : GameForm → Prop} [ClosedUnderNeg A]
    {g h : GameForm} (h1 : g ≥m A h) : (-h) ≥m A (-g) := by
  unfold MisereGe at *
  intro x h0
  have h2 := h1 (-x) (ClosedUnderNeg.neg_of x h0)
  have h4 : MisereOutcome (-h + x) = (MisereOutcome (-h + x)).Conjugate.Conjugate :=
    Eq.symm Outcome.conjugate_conjugate_eq_self
  have h5 : (MisereOutcome (-h + x)).Conjugate.Conjugate = (MisereOutcome (h + (-x))).Conjugate :=
    by simp only [outcome_conjugate_eq_outcome_neg, neg_add_rev, neg_neg, add_comm]
  rw [h4, h5]
  have h6 : (MisereOutcome (g + (-x))).Conjugate = MisereOutcome (-g + x) := by
    simp only [outcome_conjugate_eq_outcome_neg, neg_add_rev, neg_neg, add_comm]
  rw [<-h6]
  apply Outcome.outcome_ge_conjugate_le
  exact h2

@[simp]
theorem ClosedUnderNeg.neg_ge_neg_iff {A : GameForm → Prop} [ClosedUnderNeg A] (g h : GameForm) :
    (-h) ≥m A (-g) ↔ g ≥m A h := by
  constructor <;> intro h1
  · have h2 := not_ge_neg_iff.aux h1
    simp only [neg_neg] at h2
    exact h2
  · exact not_ge_neg_iff.aux h1

theorem outcome_eq_P_leftWinsGoingFirst {g gl : GameForm} (h1 : gl ∈ moves .left g)
    (h2 : MisereOutcome gl = Outcome.P) : WinsGoingFirst .left g := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h2
  by_cases h3 : WinsGoingFirst .left gl
    <;> by_cases h4 : WinsGoingFirst .right gl
    <;> simp only [h3, h4, reduceIte, reduceCtorEq] at h2
  apply WinsGoingFirst_of_moves
  simp only [Player.neg_left]
  use gl

theorem add_end_WinsGoingFirst {g h : GameForm} {p : Player} (h1 : IsEnd p g)
    (h2 : IsEnd p h) : WinsGoingFirst p (g + h) :=
  WinsGoingFirst_of_End (IsEnd.add_iff.mpr ⟨h1, h2⟩)

@[simp]
theorem one_MisereOutcome_R : MisereOutcome (1 : GameForm) = .R := by
  simp only [MisereOutcome_eq_R_iff]
  constructor
  · refine GameForm.Misere.Outcome.WinsGoingFirst_of_End ?_
    simp only [IsEnd_def, GameForm.one_def, GameForm.moves_ofSets, Player.cases]
  · rw [GameForm.Misere.Outcome.not_WinsGoingFirst]
    simp only [IsEnd_def, leftMoves_one, Set.singleton_ne_empty, not_false_eq_true,
               Set.mem_singleton_iff, Player.neg_left, forall_eq, moves_zero,
               WinsGoingFirst_of_IsEnd, and_self]

@[simp]
theorem pos_nat_MisereOutcome_R {n : ℕ} (h1 : n > 0) : MisereOutcome (n : GameForm) = .R := by
  induction n, h1 using Nat.le_induction with
  | base => simp
  | succ k h2 ih =>
    rw [Nat.cast_add, Nat.cast_one, MisereOutcome_eq_R_iff]
    constructor
    · exact WinsGoingFirst_of_End (nat_IsEnd_right (k + 1))
    · rw [GameForm.Misere.Outcome.not_WinsGoingFirst]
      simp only [IsEnd_def, leftMoves_natCast_succ, Set.singleton_ne_empty, not_false_eq_true,
                 Set.mem_singleton_iff, Player.neg_left, forall_eq, rightMoves_natCast,
                 WinsGoingFirst_of_IsEnd, and_self]

@[simp]
theorem pos_int_MisereOutcome_R {n : ℤ} (h1 : n > 0) : MisereOutcome (n : GameForm) = .R := by
  rw [<-Int.toNat_of_nonneg (Int.le_of_lt h1)]
  exact pos_nat_MisereOutcome_R (Int.pos_iff_toNat_pos.mp h1)

@[simp]
theorem neg_int_MisereOutcome_L {n : ℤ} (h1 : n < 0) : MisereOutcome (n : GameForm) = .L := by
  have h2 := pos_int_MisereOutcome_R.{u_1} (Int.neg_pos.mpr h1)
  rwa [intCast_neg, neg_MisereOutcome_R_iff] at h2

@[simp]
theorem zero_int_MisereOutcome_N {n : ℤ} (h1 : n = 0) : MisereOutcome (n : GameForm) = .N := by
  rw [h1, intCast_ofNat, Nat.cast_zero, zero_MisereOutcome_N]

theorem MiserePlayerOutcome_moves_left {g gl : GameForm} (h1 : gl ∈ moves .left g)
    (h2 : MiserePlayerOutcome gl .right = .left) : MiserePlayerOutcome g .left = .left := by
  rw [MiserePlayerOutcome_eq_iff_WinsGoingFirst, WinsGoingFirst_iff]
  apply Or.inr
  use gl
  apply And.intro h1
  simp only [Player.neg_left, Player.right_le, Player.le_right_eq]
  unfold MiserePlayerOutcome at h2
  simp only [Player.le_left, Player.neg_right, Player.le_left_eq, ite_eq_right_iff,
             reduceCtorEq, imp_false] at h2
  exact h2

theorem MiserePlayerOutcome_moves_right {g gr : GameForm} (h1 : gr ∈ moves .right g)
    (h2 : MiserePlayerOutcome gr .left = .right) : MiserePlayerOutcome g .right = .right := by
  rw [MiserePlayerOutcome_eq_iff_WinsGoingFirst, WinsGoingFirst_iff]
  refine Or.inr ⟨gr, h1, ?_⟩
  intro h3
  have h4 : MiserePlayerOutcome gr .left = .left := by
    rwa [MiserePlayerOutcome_eq_iff_WinsGoingFirst]
  rw [h4] at h2
  cases h2

end GameForm.Misere.Outcome
