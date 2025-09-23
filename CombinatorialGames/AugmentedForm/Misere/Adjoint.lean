import CombinatorialGames.AugmentedForm.Adjoint
import CombinatorialGames.AugmentedForm.Misere.Outcome

open GameForm.Adjoint
open Form.Misere.Outcome
open Form
open MisereForm
open AugmentedForm.Adjoint

namespace AugmentedForm.Misere.Adjoint

theorem outcome_add_adjoint_eq_P (g : AugmentedForm) : MisereOutcome (g + g°) = Outcome.P := by
  apply wins_opposite_outcome_eq_P
  intro p
  unfold MiserePlayerOutcome
  have h1 : ¬(WinsGoingFirst p (g + g°)) := by
    simp only [WinsGoingFirst]
    rw [AugmentedForm.WinsGoingFirst']
    simp [moves_add, Set.mem_union, Set.mem_image, exists_prop, not_or, not_and, not_exists,
          not_not, AugmentedForm.EndLike_add_iff]
    have h1 := adjoint_not_end g p
    apply And.intro (by intro h2; simpa [<-AugmentedForm.ofGameForm_IsEnd])
    intro k h1
    apply Or.elim h1 <;> intro ⟨gr, h2, h3⟩ <;> rw [<-h3] <;> clear h1 h3 k
    · have h3 : gr + gr° ∈ Form.moves (-p) (gr + g°) := by
        refine add_left_mem_moves_add ?_ gr
        have h4 := mem_adjoint_mem_opposite h2
        exact AugmentedForm.ofGameForm_moves_mem_iff.mpr h4
      rw [AugmentedForm.WinsGoingFirst']
      apply Or.inr
      use gr + gr°
      use h3
      have h4 := @outcome_eq_P_not_WinsGoingFirst AugmentedForm _ _ (- -p) (outcome_add_adjoint_eq_P gr)
      simp only [WinsGoingFirst] at h4
      exact h4
    · rw [AugmentedForm.WinsGoingFirst']
      by_cases h3 : IsEnd (-p) g
      · apply Or.inl
        simp [AugmentedForm.EndLike]
        apply Or.inr
        simp [IsEnd.add_iff, h3]
        have h4 : gr = 0 := mem_adjoint_end_opposite h2 h3
        simp [h4, IsEnd_zero]
      · apply Or.inr
        have ⟨gl, h3, h4⟩ := mem_adjoint_exists_opposite h2 h3
        rw [h4]
        use gl + gl°
        use add_right_mem_moves_add h3 (gl°)
        have h4 := @outcome_eq_P_not_WinsGoingFirst AugmentedForm _ _ (- -p) (outcome_add_adjoint_eq_P gl)
        simp only [WinsGoingFirst] at h4
        exact h4
  simp only [h1, reduceIte]
termination_by g
decreasing_by all_goals form_wf

end AugmentedForm.Misere.Adjoint
