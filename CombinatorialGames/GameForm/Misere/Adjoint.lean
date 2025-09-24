/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/

import CombinatorialGames.GameForm.Adjoint
import CombinatorialGames.GameForm.Misere.Outcome
import CombinatorialGames.AugmentedForm.Misere.Outcome

open GameForm.Adjoint
open Form.Misere.Outcome
open GameForm.Misere.Outcome
open Form
open MisereForm

namespace GameForm.Misere.Adjoint

theorem outcome_add_adjoint_eq_P (g : GameForm) : MisereOutcome (g + g°) = Outcome.P := by
  apply wins_opposite_outcome_eq_P
  intro p
  unfold MiserePlayerOutcome
  have h1 : ¬(WinsGoingFirst p (g + g°)) := by
    rw [not_WinsGoingFirst]
    simp only [IsEnd.add_iff, not_and, moves_add, Set.mem_union, Set.mem_image]
    apply And.intro (fun _ => adjoint_not_end g p)
    intro k h1
    apply Or.elim h1 <;> intro ⟨gr, h2, h3⟩ <;> rw [<-h3] <;> clear h1 h3 k
    · have h3 : gr + gr° ∈ moves (-p) (gr + g°) :=
        add_left_mem_moves_add (mem_adjoint_mem_opposite h2) gr
      apply WinsGoingFirst_of_moves
      use gr + gr°
      use h3
      exact outcome_eq_P_not_WinsGoingFirst (outcome_add_adjoint_eq_P gr)
    · by_cases h3 : IsEnd (-p) g
      · apply WinsGoingFirst_of_End
        have h4 : gr = 0 := mem_adjoint_end_opposite h2 h3
        rw [h4, add_zero]
        exact h3
      · apply WinsGoingFirst_of_moves
        have ⟨gl, h3, h4⟩ := mem_adjoint_exists_opposite h2 h3
        rw [h4]
        use gl + gl°
        use add_right_mem_moves_add h3 (gl°)
        exact outcome_eq_P_not_WinsGoingFirst (outcome_add_adjoint_eq_P gl)
  simp only [h1, reduceIte]
termination_by g
decreasing_by all_goals form_wf

end GameForm.Misere.Adjoint
