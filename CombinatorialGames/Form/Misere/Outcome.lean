/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Form.ClosedUnderNeg

public section

namespace Form.Misere.Outcome

open Form
open MisereForm

universe u

variable {G : Type (u + 1)} [Form G] [g_misere : MisereForm G]

private theorem conjugate_of_conjugates (g : G) :
    Outcome.ofPlayers
      (-(MiserePlayerOutcome g .right))
      (-(MiserePlayerOutcome g .left))
    = (MisereOutcome g).Conjugate := by
  cases h1 : MiserePlayerOutcome g .right
  <;> cases h2 : MiserePlayerOutcome g .left
  all_goals simp only [h1, h2, Outcome.Conjugate, Outcome.ofPlayers, MisereOutcome]

@[simp]
theorem outcome_eq_neg_player_conjugate (g : G) (p : Player) :
    MiserePlayerOutcome (-g) p = -(MiserePlayerOutcome g (-p)) := by
  unfold MiserePlayerOutcome
  rw [WinsGoingFirst_neg_iff g p, neg_neg]
  cases p
  · by_cases h1 : WinsGoingFirst .right g <;> simp [h1]
  · by_cases h1 : WinsGoingFirst .left g <;> simp [h1]

@[simp]
theorem outcome_conjugate_eq_outcome_neg (g : G) :
    (MisereOutcome g).Conjugate = MisereOutcome (-g) := by
  unfold Outcome.Conjugate
  cases h1 : MisereOutcome g
  all_goals
  · unfold MisereOutcome
    rw [outcome_eq_neg_player_conjugate, Player.neg_left,
        outcome_eq_neg_player_conjugate, Player.neg_right,
        conjugate_of_conjugates g, h1]
    rfl

theorem not_rightWinsGoingFirst_ge_P {g : G} (h1 : ¬WinsGoingFirst .right g) :
    MisereOutcome g ≥ Outcome.P := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
  by_cases h2 : WinsGoingFirst .left g
  all_goals simp only [h1, h2, reduceIte, ge_iff_le, le_refl, Outcome.L_ge]

theorem rightWinsGoingFirst_outcome_le_N {g : G} (h1 : WinsGoingFirst .right g) :
    MisereOutcome g ≤ Outcome.N := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
  by_cases h2 : WinsGoingFirst .left g <;> simp [h1, h2]

theorem outcome_eq_P_not_WinsGoingFirst {g : G} {p : Player}
    (h1 : MisereOutcome g = Outcome.P) : ¬WinsGoingFirst p g := by
  intro h2
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h1
  by_cases h3 : WinsGoingFirst .left g
  <;> by_cases h4 : WinsGoingFirst .right g
  <;> simp only [h3, h4, reduceIte, reduceCtorEq, Player.neg_left, Player.neg_right] at h1
  cases p
  · exact h3 h2
  · exact h4 h2

theorem wins_opposite_outcome_eq_P {g : G} (h1 : ∀ p, MiserePlayerOutcome g p = -p) :
    MisereOutcome g = Outcome.P := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [h1 .left, h1 .right]

@[simp]
theorem MisereOutcome_eq_player_iff (g : G) (p : Player) :
    (MisereOutcome g = Outcome.ofPlayer p) ↔ (WinsGoingFirst p g ∧ ¬WinsGoingFirst (-p) g) := by
  constructor <;> intro h1
  · unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h1
    by_cases h2 : WinsGoingFirst .left g
      <;> by_cases h3 : WinsGoingFirst .right g
      <;> cases p
      <;> simp only [h2, h3, Outcome.ofPlayer, Player.neg_left, Player.neg_right, reduceIte,
                     reduceCtorEq] at h1
    · exact And.intro h2 h3
    · exact And.intro h3 h2
  · unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
    cases p
    <;> simp only [Player.neg_left, Player.neg_right] at h1
    <;> simp only [h1, reduceIte, Player.neg_right, Outcome.ofPlayer]

theorem MisereOutcome_eq_L_iff {g : G} :
    (MisereOutcome g = .L) ↔ (WinsGoingFirst .left g ∧ ¬WinsGoingFirst .right g) := by
  have h1 : Outcome.L = Outcome.ofPlayer .left := by rfl
  have h2 : Player.right = -Player.left := rfl
  rw [h1, h2]
  exact MisereOutcome_eq_player_iff g Player.left

theorem MisereOutcome_eq_R_iff {g : G} :
    (MisereOutcome g = .R) ↔ (WinsGoingFirst .right g ∧ ¬WinsGoingFirst .left g) := by
  have h1 : Outcome.R = Outcome.ofPlayer .right := by rfl
  have h2 : Player.left = -Player.right := by rfl
  rw [h1, h2]
  exact MisereOutcome_eq_player_iff g Player.right

theorem MisereOutcome_eq_P_iff' {g : G} {p : Player} :
    (MisereOutcome g = .P) ↔ (¬WinsGoingFirst p g ∧ ¬WinsGoingFirst (-p) g) := by
  constructor
  · intro h1
    exact ⟨outcome_eq_P_not_WinsGoingFirst h1, outcome_eq_P_not_WinsGoingFirst h1⟩
  · intro ⟨h1, h2⟩
    unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
    cases p
    all_goals
    · simp only [Player.neg_right, Player.neg_left] at h2
      simp only [h1, h2, Player.neg_left, Player.neg_right, Player.neg_right, reduceIte]

theorem MisereOutcome_eq_P_iff {g : G} :
    (MisereOutcome g = .P) ↔ (¬WinsGoingFirst .right g ∧ ¬WinsGoingFirst .left g) := by
  rw [<-Player.neg_right]
  exact MisereOutcome_eq_P_iff'

theorem MisereOutcome_eq_N_iff {g : G} :
    (MisereOutcome g = .N) ↔ (WinsGoingFirst .left g ∧ WinsGoingFirst .right g) := by
  simp only [← MiserePlayerOutcome_eq_iff_WinsGoingFirst]
  cases h_left : MiserePlayerOutcome g .left
  <;> cases h_right : MiserePlayerOutcome g .right
  <;> simp [MisereOutcome, Outcome.ofPlayers, h_left, h_right]

@[simp]
theorem zero_MiserePlayerOutcome (p : Player) : MiserePlayerOutcome (0 : G) p = p := by
  unfold MiserePlayerOutcome
  simp only [IsEnd_zero, WinsGoingFirst_of_IsEnd, ↓reduceIte]

@[simp]
theorem zero_MisereOutcome_N : MisereOutcome (0 : G) = .N := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [zero_MiserePlayerOutcome]

@[simp]
theorem neg_MisereOutcome_R_iff {g : G} : (MisereOutcome (-g) = Outcome.R) ↔ (MisereOutcome g = Outcome.L) := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [outcome_eq_neg_player_conjugate, Player.neg_left, Player.neg_right]
  cases MiserePlayerOutcome g Player.right
  <;> cases MiserePlayerOutcome g Player.left
  <;> simp

@[simp]
theorem neg_MisereOutcome_L_iff {g : G} : (MisereOutcome (-g) = Outcome.L) ↔ (MisereOutcome g = Outcome.R) := by
  rw [<-neg_neg g, neg_MisereOutcome_R_iff, neg_neg]

@[simp]
theorem neg_MisereOutcome_N_iff {g : G} : (MisereOutcome (-g) = .N) ↔ (MisereOutcome g = .N) := by
  rw [← outcome_conjugate_eq_outcome_neg]
  cases MisereOutcome g <;> simp [Outcome.Conjugate]

-- TODO: Golf
theorem MisereOutcome_ge_iff_MiserePlayerOutcome_ge {g h : G}
    : MisereOutcome g ≥ MisereOutcome h ↔ (∀ p, MiserePlayerOutcome g p ≥ MiserePlayerOutcome h p) := by
  apply Iff.intro <;> intro h1
  · intro p; cases p
    · simp [MisereOutcome, Outcome.ofPlayers] at h1
      cases h4 : MiserePlayerOutcome g Player.left
      <;> cases h5 : MiserePlayerOutcome g Player.right
      <;> cases h6 : MiserePlayerOutcome h Player.left
      <;> cases h7 : MiserePlayerOutcome h Player.right
      <;> simp [h4, h5, h6, h7] at h1
      <;> try decide
      · absurd h1
        decide
      · absurd h1
        decide
    · simp [MisereOutcome, Outcome.ofPlayers] at h1
      cases h4 : MiserePlayerOutcome g Player.left
      <;> cases h5 : MiserePlayerOutcome g Player.right
      <;> cases h6 : MiserePlayerOutcome h Player.left
      <;> cases h7 : MiserePlayerOutcome h Player.right
      <;> simp [h4, h5, h6, h7] at h1
      <;> try decide
      · absurd h1
        decide
      · absurd h1
        decide
  · have h2 := h1 .left
    have h3 := h1 .right
    cases h4 : MiserePlayerOutcome g Player.left
    <;> cases h5 : MiserePlayerOutcome g Player.right
    <;> cases h6 : MiserePlayerOutcome h Player.left
    <;> cases h7 : MiserePlayerOutcome h Player.right
    <;> simp [MisereOutcome, Outcome.ofPlayers, h4, h5, h6, h7] at ⊢ h2 h3
    · exact (Player.left_le_right h3).elim
    · exact (Player.left_le_right h3).elim
    · exact (Player.left_le_right h2).elim
    · exact (Player.left_le_right h2).elim
    · exact (Player.left_le_right h2).elim
    · exact (Player.left_le_right h2).elim
    · exact (Player.left_le_right h3).elim

@[expose] def MisereEq (A : G → Prop) (g h : G) : Prop :=
  ∀ (x : G), A x → MisereOutcome (g + x) = MisereOutcome (h + x)

macro x:term:51 " =m " u:term:max y:term:51 : term => `(MisereEq $u $x $y)

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab MisereEq]
meta def delabMisereEq : Delab := do
  let y ← withAppArg delab
  let x ← withAppFn do withAppArg delab
  let u ← withAppFn do withAppFn do withAppArg delab
  `($x =m $u $y)

theorem MisereEq_symm {A : G → Prop} {g h : G} (h1 : g =m A h) : h =m A g := by
  intro x h2
  have h3 := h1 x h2
  exact Eq.symm h3

theorem MisereEq_trans {A : G → Prop} {g h k : G} (h1 : g =m A h) (h2 : h =m A k) :
    g =m A k := by
  unfold MisereEq at *
  intro x h3
  exact cast (congrArg (Eq (MisereOutcome (g + x))) (h2 x h3)) (h1 x h3)

@[expose] def MisereGe (A : G → Prop) (g h : G) : Prop :=
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

theorem MisereGe_antisymm {A : G → Prop} {g h : G} (h1 : g ≥m A h) (h2 : h ≥m A g) :
    g =m A h := fun x h3 =>
  PartialOrder.le_antisymm (MisereOutcome (g + x)) (MisereOutcome (h + x)) (h2 x h3) (h1 x h3)

theorem MisereGe_trans {A : G → Prop} {g h k : G} (h1 : g ≥m A h) (h2 : h ≥m A k) :
    g ≥m A k := by
  unfold MisereGe at *
  intro x h3
  exact le_trans (h2 x h3) (h1 x h3)

theorem MisereGe_rw_left {A : G → Prop} {a b c : G} (h2 : b =m A c) (h1 : b ≥m A a) : c ≥m A a := by
  unfold MisereGe at h1 ⊢
  unfold MisereEq at h2
  intro x hx
  rw [<-h2 x hx]
  exact h1 x hx

theorem MisereGe_rw_right {A : G → Prop} {a b c : G} (h2 : b =m A c) (h1 : a ≥m A c) : a ≥m A b := by
  unfold MisereGe at h1 ⊢
  unfold MisereEq at h2
  intro x hx
  rw [h2 x hx]
  exact h1 x hx

theorem MisereGe_of_subset (U : G → Prop) {V : G → Prop}
    (h_v_subset_u : ∀g, V g → U g) (g h : G) (h2 : g ≥m U h) : g ≥m V h := by
  unfold MisereGe at h2 ⊢
  intro x hv
  exact h2 x (h_v_subset_u x hv)

@[simp]
theorem MisereGe_refl {A : G → Prop} (g : G) : g ≥m A g := by
  unfold MisereGe
  intro x h3
  exact le_refl MisereOutcome (g + x)

theorem not_MisereEq_of_not_MisereGe {A : G → Prop} {g h : G} (h1 : ¬(g ≥m A h)) :
    ¬(g =m A h) := by
  simp only [MisereGe, ge_iff_le, not_forall] at h1
  obtain ⟨x, ⟨h1, h2⟩⟩ := h1
  simp only [MisereEq, not_forall]
  use x
  use h1
  exact Ne.symm (ne_of_not_le h2)

private theorem ClosedUnderNeg.not_ge_neg_iff.aux {A : G → Prop} [ClosedUnderNeg A]
    {g h : G} (h1 : g ≥m A h) : (-h) ≥m A (-g) := by
  unfold MisereGe at *
  intro x h0
  have h2 := h1 (-x) (ClosedUnderNeg.neg_iff.mpr h0)
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
theorem ClosedUnderNeg.neg_ge_neg_iff {A : G → Prop} [ClosedUnderNeg A]
    (g h : G) : (-h) ≥m A (-g) ↔ g ≥m A h := by
  constructor <;> intro h1
  · have h2 := not_ge_neg_iff.aux h1
    simp only [neg_neg] at h2
    exact h2
  · exact not_ge_neg_iff.aux h1

theorem outcome_eq_P_leftWinsGoingFirst {g gl : G} (h1 : gl ∈ moves .left g)
    (h2 : MisereOutcome gl = Outcome.P) : WinsGoingFirst .left g := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h2
  by_cases h3 : WinsGoingFirst .left gl
    <;> by_cases h4 : WinsGoingFirst .right gl
    <;> simp only [h3, h4, reduceIte, reduceCtorEq] at h2
  apply WinsGoingFirst_of_moves
  simp only [Player.neg_left]
  use gl

theorem add_end_WinsGoingFirst {g h : G} {p : Player} (h1 : IsEnd p g)
    (h2 : IsEnd p h) : WinsGoingFirst p (g + h) :=
  WinsGoingFirst_of_IsEnd (IsEnd.add_iff.mpr ⟨h1, h2⟩)

theorem MiserePlayerOutcome_moves_left {g gl : G} (h1 : gl ∈ moves .left g)
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

theorem MiserePlayerOutcome_moves_right {g gr : G} (h1 : gr ∈ moves .right g)
    (h2 : MiserePlayerOutcome gr .left = .right) : MiserePlayerOutcome g .right = .right := by
  rw [MiserePlayerOutcome_eq_iff_WinsGoingFirst, WinsGoingFirst_iff]
  refine Or.inr ⟨gr, h1, ?_⟩
  intro h3
  have h4 : MiserePlayerOutcome gr .left = .left := by
    rwa [MiserePlayerOutcome_eq_iff_WinsGoingFirst]
  rw [h4] at h2
  cases h2

end Form.Misere.Outcome
