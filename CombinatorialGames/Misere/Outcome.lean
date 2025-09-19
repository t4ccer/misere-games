/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/

import CombinatorialGames.Outcome
import CombinatorialGames.GameForm.Birthday
import CombinatorialGames.Form.Short

namespace GameForm.Misere.Outcome

open MisereForm

private def WinsGoingFirst' (g : GameForm) (p : Player) : Prop :=
  g.moves p = ∅ ∨ (∃ g', ∃ (_ : g' ∈ g.moves p), ¬WinsGoingFirst' g' (-p))
termination_by g
decreasing_by form_wf

instance : MisereForm GameForm where
  WinsGoingFirst p g := WinsGoingFirst' g p

theorem WinsGoingFirst_def (p : Player) (g : GameForm) :
  WinsGoingFirst p g = ((moves p g = ∅) ∨ (∃ g', ∃ (_ : g' ∈ g.moves p), ¬WinsGoingFirst (-p) g')) := by
  unfold WinsGoingFirst
  unfold instMisereForm
  simp only [exists_prop, eq_iff_iff]
  rw [WinsGoingFirst']
  simp only [exists_prop]

def MisereEq (A : GameForm → Prop) (g h : GameForm) : Prop :=
  ∀ (x : GameForm), A x → MisereOutcome (g + x) = MisereOutcome (h + x)

/-- `G =m A H` means that G =_A H -/
macro_rules | `($x =m $u $y) => `(MisereEq $u $x $y)

theorem MisereEq_symm {A : GameForm → Prop} {g h : GameForm} (h1 : g =m A h) : h =m A g := by
  intro x h2
  have h3 := h1 x h2
  exact Eq.symm h3

def MisereGe (A : GameForm → Prop) (g h : GameForm) : Prop :=
  ∀ x, (A x → MisereOutcome (g + x) ≥ MisereOutcome (h + x))

/-- `G ≥m A H` means that G ≥_A H -/
macro_rules | `($x ≥m $u $y) => `(MisereGe $u $x $y)

theorem MisereGe_antisymm {A : GameForm → Prop} {g h : GameForm} (h1 : g ≥m A h) (h2 : h ≥m A g) :
    g =m A h := fun x h3 =>
  PartialOrder.le_antisymm (MisereOutcome (g + x)) (MisereOutcome (h + x)) (h2 x h3) (h1 x h3)


theorem End_WinsGoingFirst {g : GameForm} {p : Player} (h1 : g.IsEnd p) : WinsGoingFirst p g := by
  rw [WinsGoingFirst_def]
  exact Or.inl h1

theorem not_MisereEq_of_not_MisereGe {A : GameForm → Prop} {g h : GameForm} (h1 : ¬(g ≥m A h)) :
    ¬(g =m A h) := by
  simp only [MisereGe, ge_iff_le, not_forall] at h1
  obtain ⟨x, ⟨h1, h2⟩⟩ := h1
  simp only [MisereEq, not_forall]
  use x
  use h1
  exact Ne.symm (ne_of_not_le h2)

@[simp]
theorem neg_WinsGoingFirst_iff_WinsGoingFirst_player_neg (g : GameForm) (p : Player) :
    (WinsGoingFirst p (-g)) ↔ (WinsGoingFirst (-p) g) := by
  constructor
    <;> intro h1
    <;> rw [WinsGoingFirst_def] at h1
    <;> apply Or.elim h1
    <;> intro h1
  · exact End_WinsGoingFirst (GameForm.end_neg_iff_player_neg.mp h1)
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [WinsGoingFirst_def, neg_neg]
    simp only [exists_prop]
    apply Or.inr
    use -gp
    simp only [GameForm.moves_neg, Set.mem_neg] at h1
    exact And.intro h1 ((neg_WinsGoingFirst_iff_WinsGoingFirst_player_neg gp p).not.mpr h2)
  · exact End_WinsGoingFirst (GameForm.end_neg_iff_player_neg.mpr h1)
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [WinsGoingFirst_def]
    apply Or.inr
    use -gp
    simp only [GameForm.moves_neg, Set.involutiveNeg, Set.mem_neg, neg_neg, exists_prop]
    apply And.intro h1
    have h3 := (neg_WinsGoingFirst_iff_WinsGoingFirst_player_neg (-gp) p).not.mp
    rw [neg_neg] at h2 h3
    exact h3 h2
termination_by Form.birthday g
decreasing_by
  · simp only [GameForm.moves_neg, Set.mem_neg] at h1
    rw [Form.lt_birthday_iff]
    cases p
    · apply Or.inr
      use -gp
      apply And.intro h1
      rw [GameForm.birthday_neg]
    · apply Or.inl
      use -gp
      apply And.intro h1
      rw [GameForm.birthday_neg]
  · rw [GameForm.birthday_neg, Form.lt_birthday_iff]
    cases p
    · apply Or.inr
      use gp
      exact And.intro h1 (Preorder.le_refl (Form.birthday gp))
    · apply Or.inl
      use gp
      exact And.intro h1 (Preorder.le_refl (Form.birthday gp))

class ClosedUnderNeg (A : GameForm → Prop) where
  neg_of (g : GameForm) (h1 : A g) : A (-g)

instance : ClosedUnderNeg GameForm.Short where
  neg_of _ h := GameForm.Short.neg_iff.mpr h

private theorem conjugate_of_conjugates (g : GameForm) :
    Outcome.ofPlayers
      (-(MiserePlayerOutcome g .right))
      (-(MiserePlayerOutcome g .left))
    = (MisereOutcome g).Conjugate := by
  cases h1 : MiserePlayerOutcome g .right
  <;> cases h2 : MiserePlayerOutcome g .left
  all_goals simp only [h1, h2, Outcome.Conjugate, Outcome.ofPlayers, MisereOutcome]

@[simp]
theorem outcome_eq_neg_player_conjugate (g : GameForm) (p : Player) :
    MiserePlayerOutcome (-g) p = -(MiserePlayerOutcome g (-p)) := by
  unfold MiserePlayerOutcome
  rw [neg_WinsGoingFirst_iff_WinsGoingFirst_player_neg g p, neg_neg]
  cases p
  · by_cases h1 : WinsGoingFirst .right g <;> simp [h1]
  · by_cases h1 : WinsGoingFirst .left g <;> simp [h1]

@[simp]
theorem outcome_conjugate_eq_outcome_neg (g : GameForm) :
    (MisereOutcome g).Conjugate = MisereOutcome (-g) := by
  unfold Outcome.Conjugate
  cases h1 : MisereOutcome g
  all_goals
  · unfold MisereOutcome
    rw [outcome_eq_neg_player_conjugate, Player.neg_left,
        outcome_eq_neg_player_conjugate, Player.neg_right,
        conjugate_of_conjugates g, h1]
    rfl

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

theorem not_rightWinsGoingFirst_ge_P {g : GameForm} (h1 : ¬WinsGoingFirst .right g) :
    MisereOutcome g ≥ Outcome.P := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
  by_cases h2 : WinsGoingFirst .left g
  all_goals simp only [h1, h2, reduceIte, ge_iff_le, le_refl, Outcome.L_ge]

theorem rightWinsGoingFirst_outcome_le_N {g : GameForm} (h1 : WinsGoingFirst .right g) :
    MisereOutcome g ≤ Outcome.N := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
  by_cases h2 : WinsGoingFirst .left g <;> simp [h1, h2]

theorem outcome_eq_P_leftWinsGoingFirst {g gl : GameForm} (h1 : gl ∈ g.moves .left)
    (h2 : MisereOutcome gl = Outcome.P) : WinsGoingFirst .left g := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h2
  by_cases h3 : WinsGoingFirst .left gl
    <;> by_cases h4 : WinsGoingFirst .right gl
    <;> simp only [h3, h4, reduceIte, reduceCtorEq] at h2
  rw [WinsGoingFirst_def]
  apply Or.inr
  simp only [Player.neg_left, exists_prop]
  use gl

theorem outcome_eq_P_not_WinsGoingFirst {g : GameForm} {p : Player}
    (h1 : MisereOutcome g = Outcome.P) : ¬WinsGoingFirst p g := by
  intro h2
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h1
  by_cases h3 : WinsGoingFirst .left g
  <;> by_cases h4 : WinsGoingFirst .right g
  <;> simp only [h3, h4, reduceIte, reduceCtorEq, Player.neg_left, Player.neg_right] at h1
  cases p
  · exact h3 h2
  · exact h4 h2

theorem add_end_WinsGoingFirst {g h : GameForm} {p : Player} (h1 : g.IsEnd p)
    (h2 : h.IsEnd p) : WinsGoingFirst p (g + h) :=
  End_WinsGoingFirst (GameForm.IsEnd.add_iff.mpr ⟨h1, h2⟩)

theorem wins_opposite_outcome_eq_P {g : GameForm} (h1 : ∀ p, MiserePlayerOutcome g p = -p) :
    MisereOutcome g = Outcome.P := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [h1 .left, h1 .right]

@[simp]
theorem MisereOutcome_eq_player_iff (g : GameForm) (p : Player) :
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

@[simp]
theorem MisereOutcome_eq_L_iff {g : GameForm} :
    (MisereOutcome g = .L) ↔ (WinsGoingFirst .left g ∧ ¬WinsGoingFirst .right g) := by
  have h1 : Outcome.L = Outcome.ofPlayer .left := rfl
  have h2 : Player.right = -Player.left := rfl
  rw [h1, h2]
  exact MisereOutcome_eq_player_iff g Player.left

@[simp]
theorem MisereOutcome_eq_R_iff {g : GameForm} :
    (MisereOutcome g = .R) ↔ (WinsGoingFirst .right g ∧ ¬WinsGoingFirst .left g) := by
  have h1 : Outcome.R = Outcome.ofPlayer .right := rfl
  have h2 : Player.left = -Player.right := rfl
  rw [h1, h2]
  exact MisereOutcome_eq_player_iff g Player.right

end GameForm.Misere.Outcome
