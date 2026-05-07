module

public import CombinatorialGames.Form.Adjoint
public import CombinatorialGames.Form.Misere.Outcome

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Form.Misere.Outcome

public section

namespace Form.Misere.Adjoint

theorem outcome_add_adjoint_eq_P (g : G) : MisereOutcome (g + g°) = Outcome.P := by
  apply MisereOutcome_P_of_MiserePlayerOutcome_neg
  intro p
  unfold MiserePlayerOutcome
  have h1 : ¬(WinsGoingFirst p (g + g°)) := by
    rw [not_WinsGoingFirst]
    simp only [IsEndLike.add_iff, Form.Adjoint.adjoint_not_EndLike, and_false, not_false_eq_true,
               moves_add, Set.mem_union, Set.mem_image, true_and]
    intro k h1
    apply Or.elim h1 <;> intro ⟨gr, h2, h3⟩ <;> rw [<-h3] <;> clear h1 h3 k
    · have h3 : gr + gr° ∈ moves (-p) (gr + g°) :=
        add_left_mem_moves_add (Form.Adjoint.mem_adjoint_mem_opposite h2) gr
      apply WinsGoingFirst_of_moves
      use gr + gr°, h3
      exact not_WinsGoingFirst_of_MisereOutcome_P (outcome_add_adjoint_eq_P gr)
    · by_cases h3 : IsEnd (-p) g
      · apply WinsGoingFirst_of_IsEnd
        have h4 : gr = 0 := Form.Adjoint.mem_adjoint_end_opposite h2 h3
        simp only [h3, h4, add_zero]
      · apply WinsGoingFirst_of_moves
        have ⟨gl, h3, h4⟩ := Form.Adjoint.mem_adjoint_exists_opposite h2 h3
        rw [h4]
        use gl + gl°, add_right_mem_moves_add h3 (gl°)
        exact not_WinsGoingFirst_of_MisereOutcome_P (outcome_add_adjoint_eq_P gl)
  simp only [h1, reduceIte]
termination_by g
decreasing_by all_goals form_wf

end Form.Misere.Adjoint
