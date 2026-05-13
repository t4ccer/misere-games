/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import CombinatorialGames.Form.Adjoint
public import CombinatorialGames.Form.Misere.Outcome

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Form.Misere.Outcome

public section

namespace Form.Misere.Adjoint

/--
[Siegel, (Proposition 3.3 on p. 228)][siegel:CanonicalPartizan:2015] showed
that, for every short game form $G$, the sum $G+G^\circ$ is always a
$\mathscr{P}$-position. (See also [Siegel, (Proposition 6.4 on p.
270)][siegel:CombinatorialGameTheory:2013].) [Siegel, (Proposition 5.7 on p.
214)][siegel:GeneralDeadendingUniverse:2025] later extended this result to
short augmented forms. The present result generalises further to transfinite
augmented forms.
-/
theorem misereOutcome_add_adjoint_eq_P (g : G) : MisereOutcome (g + g°) = Outcome.P := by
  apply misereOutcome_P_of_miserePlayerOutcome_neg
  intro p
  unfold MiserePlayerOutcome
  have h1 : ¬(WinsGoingFirst p (g + g°)) := by
    rw [not_winsGoingFirst_iff]
    simp only [IsEndLike.add_iff, Form.Adjoint.adjoint_not_isEndLike, and_false, not_false_eq_true,
               moves_add, Set.mem_union, Set.mem_image, true_and]
    intro k h1
    apply Or.elim h1 <;> intro ⟨gr, h2, h3⟩ <;> rw [<-h3] <;> clear h1 h3 k
    · have h3 : gr + gr° ∈ moves (-p) (gr + g°) :=
        add_left_mem_moves_add (Form.Adjoint.mem_adjoint_mem_opposite h2) gr
      apply winsGoingFirst_of_moves
      use gr + gr°, h3
      exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P gr)
    · by_cases h3 : IsEnd (-p) g
      · apply winsGoingFirst_of_isEnd
        have h4 : gr = 0 := Form.Adjoint.mem_adjoint_end_opposite h2 h3
        simp only [h3, h4, add_zero]
      · apply winsGoingFirst_of_moves
        have ⟨gl, h3, h4⟩ := Form.Adjoint.mem_adjoint_exists_opposite h2 h3
        rw [h4]
        use gl + gl°, add_right_mem_moves_add h3 (gl°)
        exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P gl)
  simp only [h1, reduceIte]
termination_by g
decreasing_by all_goals form_wf

end Form.Misere.Adjoint
