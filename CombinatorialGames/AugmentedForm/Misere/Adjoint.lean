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
    rw [not_WinsGoingFirst]
    constructor
    · simp only [not_EndLike]
      constructor
      · rw [hasTombstone_add]
        intro h1
        apply Or.elim h1 <;> intro ⟨h1, h2⟩
        · exact adjoint_not_EndLike h2
        · exact not_hasTombstone_ofGameForm (g°) p h1
      · simp only [IsEnd.add_iff, not_and]
        intro _
        have h1 := adjoint_not_end g p
        have h2 := EndLike_ofGameForm_iff.not.mpr h1
        rw [not_EndLike] at h2
        exact h2.right
    simp only [moves_add, Set.mem_union, Set.mem_image]
    intro k h1
    apply Or.elim h1 <;> intro ⟨gr, h2, h3⟩ <;> rw [<-h3] <;> clear h1 h3 k
    · have h3 : gr + gr° ∈ Form.moves (-p) (gr + g°) := by
        refine add_left_mem_moves_add ?_ gr
        have h4 := mem_adjoint_mem_opposite h2
        exact AugmentedForm.ofGameForm_moves_mem_iff.mpr h4
      apply WinsGoingFirst_of_moves
      use gr + gr°, h3
      exact outcome_eq_P_not_WinsGoingFirst (outcome_add_adjoint_eq_P gr)
    · by_cases h3 : IsEnd (-p) g
      · apply WinsGoingFirst_of_End
        simp only [IsEnd.add_iff, h3, true_and]
        have h4 : gr = 0 := mem_adjoint_end_opposite h2 h3
        simp only [h4, IsEnd_zero]
      · apply WinsGoingFirst_of_moves
        have ⟨gl, h3, h4⟩ := mem_adjoint_exists_opposite h2 h3
        rw [h4]
        use gl + gl°, add_right_mem_moves_add h3 (gl°)
        exact outcome_eq_P_not_WinsGoingFirst (outcome_add_adjoint_eq_P gl)
  simp only [h1, reduceIte]
termination_by g
decreasing_by all_goals form_wf

end AugmentedForm.Misere.Adjoint
