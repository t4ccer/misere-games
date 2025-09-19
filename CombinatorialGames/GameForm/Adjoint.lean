/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/

import CombinatorialGames.GameForm.Special
import Mathlib.Data.Countable.Small

namespace GameForm

open Form (Short)
open Classical in
noncomputable def Adjoint (g : GameForm) : GameForm :=
  if g = (0 : GameForm) then ⋆
  else if g.IsEnd .left then !{Set.range fun gr : g.moves .right => Adjoint gr|{0}}
  else if g.IsEnd .right then !{{0}|Set.range fun gl : g.moves .left => Adjoint gl}
  else !{ Set.range fun gr : g.moves .right => Adjoint gr
        | Set.range fun gl : g.moves .left => Adjoint gl}
termination_by g
decreasing_by form_wf

notation g"°" => Adjoint g

namespace Adjoint

@[simp]
theorem adjont_zero_eq_star : 0° = ⋆ := by
  unfold Adjoint
  simp only [reduceIte]

theorem adjoint_not_end (g : GameForm) (p : Player) : ¬((g°).IsEnd p) := by
  unfold Adjoint GameForm.IsEnd
  by_cases h1 : g = 0 <;> simp [h1]
  by_cases h2 : g.moves .left = ∅ <;> cases p <;> simp [h2]
  all_goals by_cases h3 : g.moves .right = ∅ <;> simp [h2, h3]
  exact h1 (GameForm.leftEnd_rightEnd_eq_zero h2 h3)

-- TODO: Combine
private theorem mem_leftMoves_mem_adjoint_rightMoves {g gl : GameForm} (h1 : gl ∈ g.moves .left) :
    gl° ∈ (g°).moves .right := by
  rw [Adjoint, GameForm.IsEnd, GameForm.IsEnd]
  have h2 : g ≠ 0 := GameForm.mem_moves_ne_zero h1
  by_cases h3 : g.moves .left = ∅ <;> by_cases h4 : g.moves .right = ∅ <;> simp [*]
  · simp [h3] at h1
  · simp [h3] at h1
  · use gl
  · use gl

private theorem mem_rightMoves_mem_adjoint_leftMoves {g gr : GameForm} (h1 : gr ∈ g.moves .right) :
    gr° ∈ (g°).moves .left := by
  rw [Adjoint, GameForm.IsEnd, GameForm.IsEnd]
  have h2 : g ≠ 0 := GameForm.mem_moves_ne_zero h1
  by_cases h3 : g.moves .left = ∅ <;> by_cases h4 : g.moves .right = ∅ <;> simp [*]
  · simp [h4] at h1
  · use gr
  · simp [h4] at h1
  · use gr

theorem mem_adjoint_mem_opposite {g gp : GameForm} {p : Player}
    (h1 : gp ∈ g.moves p) : gp° ∈ (g°).moves (-p) := by
  cases p
  · exact mem_leftMoves_mem_adjoint_rightMoves h1
  · exact mem_rightMoves_mem_adjoint_leftMoves h1

theorem mem_adjoint_exists_opposite {g gp : GameForm} {p : Player} (h1 : gp ∈ g°.moves p)
    (h2 : ¬(g.IsEnd (-p))) : ∃ gnp ∈ g.moves (-p), gp = gnp° := by
  unfold Adjoint at h1
  have h3 : g ≠ 0 := GameForm.not_end_ne_zero h2
  simp [h3] at h1
  by_cases h4 : g.IsEnd p <;> cases p
  any_goals rw [Player.neg_left] at h2
  any_goals rw [Player.neg_right] at h2
  all_goals
  · simp only [h2, h4, reduceIte, moves_ofSets, Player.cases, Set.mem_range, Subtype.exists,
               exists_prop] at h1
    obtain ⟨gnp, h5, h6⟩ := h1
    use gnp
    exact And.symm ⟨Eq.symm h6, h5⟩

theorem mem_adjoint_end_opposite {g gp : GameForm} {p : Player}
    (h1 : gp ∈ g°.moves p) (h2 : g.IsEnd (-p)) : gp = 0 := by
  unfold Adjoint at h1
  by_cases h3 : g.IsEnd p
  · have h4 : g = 0 := GameForm.both_ends_eq_zero h3 h2
    simp only [h4, ↓reduceIte, star, moves_ofSets, Set.mem_singleton_iff] at h1
    exact h1
  · have h4 : g ≠ 0 := not_end_ne_zero h3
    simp [h4] at h1
    cases p
    · rw [Player.neg_left] at h2
      simp [h2, h3] at h1
      exact h1
    · rw [Player.neg_right] at h2
      simp [h2] at h1
      exact h1

instance short_adjoint (g : GameForm) [h1 : Short g] : Short (g°) := by
  sorry
--  unfold Adjoint
--  by_cases h2 : g = 0 <;> simp only [h2, reduceIte, GameForm.instShortStar]
--  by_cases h3 : g.IsEnd .left <;> simp [h3, reduceIte]
--    <;> by_cases h4 : g.IsEnd .right
--    <;> rw [GameForm.short_def]
--    <;> intro p
--    <;> cases p
--  any_goals simp only [Player.cases, Set.finite_singleton, Set.mem_range, Set.mem_singleton_iff,
--                       Short.zero, Subtype.exists, and_imp, and_self, exists_prop,
--                       forall_apply_eq_imp_iff₂, forall_eq, forall_exists_index, moves_ofSets, h4,
--                       reduceIte]
--  all_goals constructor
--  any_goals exact Set.finite_range (fun gr : g.moves .right => Adjoint gr)
--  any_goals exact Set.finite_range (fun gl : g.moves .left => Adjoint gl)
--  all_goals
--  · intro gr h5
--    have _ : Short gr := Short.of_mem_moves h5
--    exact short_adjoint gr
--termination_by g
--decreasing_by all_goals form_wf

end Adjoint
end GameForm
