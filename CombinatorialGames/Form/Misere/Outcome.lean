/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Form

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

end Form.Misere.Outcome
