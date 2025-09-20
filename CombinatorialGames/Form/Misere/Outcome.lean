/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/


import CombinatorialGames.Form

namespace Form.Misere.Outcome

open Form
open MisereForm

universe u

variable {G : Type u} [g_misere : MisereForm G]

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

@[simp]
theorem MisereOutcome_eq_L_iff {g : G} :
    (MisereOutcome g = .L) ↔ (WinsGoingFirst .left g ∧ ¬WinsGoingFirst .right g) := by
  have h1 : Outcome.L = Outcome.ofPlayer .left := rfl
  have h2 : Player.right = -Player.left := rfl
  rw [h1, h2]
  exact MisereOutcome_eq_player_iff g Player.left

@[simp]
theorem MisereOutcome_eq_R_iff {g : G} :
    (MisereOutcome g = .R) ↔ (WinsGoingFirst .right g ∧ ¬WinsGoingFirst .left g) := by
  have h1 : Outcome.R = Outcome.ofPlayer .right := rfl
  have h2 : Player.left = -Player.right := rfl
  rw [h1, h2]
  exact MisereOutcome_eq_player_iff g Player.right

end Form.Misere.Outcome
