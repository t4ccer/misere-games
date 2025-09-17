/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/

import CombinatorialGames.GameForm.Adjoint
import CombinatorialGames.Misere.Outcome

open GameForm.Adjoint
open GameForm.Misere.Outcome

open MisereForm

theorem outcome_add_adjoint_eq_P (g : GameForm) : MisereOutcome (g + g°) = Outcome.P := by
  apply wins_opposite_outcome_eq_P
  intro p
  unfold MiserePlayerOutcome
  have h1 : ¬(WinsGoingFirst p (g + g°)) := by
    rw [WinsGoingFirst_def]
    simp only [GameForm.moves_add, Set.union_empty_iff, Set.image_eq_empty, Set.mem_union,
               Set.mem_image, exists_prop, not_or, not_and, not_exists, not_not]
    apply And.intro (fun _ => adjoint_not_end g p)
    intro k h1
    apply Or.elim h1 <;> intro ⟨gr, h2, h3⟩ <;> rw [<-h3] <;> clear h1 h3 k
    · have h3 : gr + gr° ∈ (gr + g°).moves (-p) :=
        GameForm.add_left_mem_moves_add (mem_adjoint_mem_opposite h2) gr
      rw [WinsGoingFirst_def]
      apply Or.inr
      use gr + gr°
      use h3
      exact outcome_eq_P_not_WinsGoingFirst (outcome_add_adjoint_eq_P gr)
    · rw [WinsGoingFirst_def]
      by_cases h3 : g.IsEnd (-p)
      · apply Or.inl
        have h4 : gr = 0 := mem_adjoint_end_opposite h2 h3
        rw [h4, add_zero]
        exact h3
      · apply Or.inr
        have ⟨gl, h3, h4⟩ := mem_adjoint_exists_opposite h2 h3
        rw [h4]
        use gl + gl°
        use GameForm.add_right_mem_moves_add h3 (gl°)
        exact outcome_eq_P_not_WinsGoingFirst (outcome_add_adjoint_eq_P gl)
  simp only [h1, reduceIte]
termination_by g
decreasing_by all_goals form_wf
