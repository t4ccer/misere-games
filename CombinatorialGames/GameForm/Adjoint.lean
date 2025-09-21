/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/

import CombinatorialGames.GameForm.Special
import Mathlib.Data.Countable.Small

namespace GameForm

open Form

universe u

variable {G : Type (u + 1)} [g_misere : Form G]

open Classical in
noncomputable def Adjoint (g : G) : GameForm.{u} :=
  have := Form.moves_small.{u} .left g
  have := Form.moves_small.{u} .right g
  if IsEnd .left g ∧ IsEnd .right g then ⋆
  else if IsEnd .left g then !{Set.range fun gr : Form.moves .right g => Adjoint (gr : G)|{0}}
  else if IsEnd .right g then !{{0}|Set.range fun gl : Form.moves .left g => Adjoint (gl : G)}
  else !{ Set.range fun gr : Form.moves .right g => Adjoint (gr : G)
        | Set.range fun gl : Form.moves .left g => Adjoint (gl : G)}
termination_by g
decreasing_by form_wf

notation g"°" => Adjoint g

namespace Adjoint

@[simp]
theorem adjont_zero_eq_star : (0 : G)° = ⋆ := by
  unfold Adjoint
  simp only [IsEnd_zero, and_self, ↓reduceIte]

theorem adjoint_not_end (g : G) (p : Player) : ¬(IsEnd p (g°)) := by
  unfold Adjoint IsEnd
  by_cases h1 : Form.moves .left g = ∅ ∧ Form.moves .right g = ∅ <;> simp [h1]
  all_goals by_cases h2 : Form.moves .left g = ∅ <;> cases p <;> simp [Form.moves]
  all_goals by_cases h3 : Form.moves .right g = ∅ <;> simp [h2, h3]
  rw [not_and] at h1
  exact h1 h2 h3

-- TODO: Combine
private theorem mem_leftMoves_mem_adjoint_rightMoves {g gl : G} (h1 : gl ∈ Form.moves .left g) :
    gl° ∈ (g°).moves .right := by
  rw [Adjoint, IsEnd, IsEnd]
  have h2 : g ≠ 0 := mem_moves_ne_zero h1
  by_cases h3 : Form.moves .left g = ∅ <;> by_cases h4 : Form.moves .right g = ∅ <;> simp [*]
  · simp [h3] at h1
  · simp [h3] at h1
  · use gl
  · use gl

private theorem mem_rightMoves_mem_adjoint_leftMoves {g gr : G} (h1 : gr ∈ Form.moves .right g) :
    gr° ∈ (g°).moves .left := by
  rw [Adjoint, IsEnd, IsEnd]
  have h2 : g ≠ 0 := mem_moves_ne_zero h1
  by_cases h3 : Form.moves .left g = ∅ <;> by_cases h4 : Form.moves .right g = ∅ <;> simp [*]
  · simp [h4] at h1
  · use gr
  · simp [h4] at h1
  · use gr

theorem mem_adjoint_mem_opposite {g gp : G} {p : Player}
    (h1 : gp ∈ Form.moves p g) : gp° ∈ Form.moves (-p) (g°) := by
  cases p
  · exact mem_leftMoves_mem_adjoint_rightMoves h1
  · exact mem_rightMoves_mem_adjoint_leftMoves h1

theorem mem_adjoint_exists_opposite {g : G} {gp : GameForm} {p : Player} (h1 : gp ∈ g°.moves p)
    (h2 : ¬(IsEnd (-p) g)) : ∃ gnp ∈ Form.moves (-p) g, gp = gnp° := by
  unfold Adjoint at h1
  have h3 : g ≠ 0 := not_IsEnd_ne_zero h2
  by_cases h4 : IsEnd p g <;> cases p
  any_goals rw [Player.neg_left] at h2
  any_goals rw [Player.neg_right] at h2
  all_goals
  · simp only [h4, h2, and_false, false_and, ↓reduceIte, moves_ofSets, Player.cases,
               Set.mem_range, Subtype.exists, exists_prop] at h1
    obtain ⟨gnp, h5, h6⟩ := h1
    use gnp
    exact And.symm ⟨Eq.symm h6, h5⟩

theorem mem_adjoint_end_opposite {g : G} {gp : GameForm} {p : Player}
    (h1 : gp ∈ g°.moves p) (h2 : IsEnd (-p) g) : gp = 0 := by
  unfold Adjoint at h1
  by_cases h3 : IsEnd p g
  · cases p
    all_goals
    · simp only [Player.neg_left, Player.neg_right] at h2
      simp only [h2, h3, and_self, ↓reduceIte, moves_star, Set.mem_singleton_iff] at h1
      exact h1
  · have h4 : g ≠ 0 := not_IsEnd_ne_zero h3
    cases p
    all_goals
    · simp only [Player.neg_left, Player.neg_right] at h2
      simp only [h2, h3, and_true, and_false, ↓reduceIte, moves_ofSets, Player.cases,
                 Set.mem_singleton_iff] at h1
      exact h1

instance short_adjoint (g : G) [h1 : Short g] : Short (g°) := by
  unfold Adjoint
  by_cases h2 : g = 0 <;> simp [h2, reduceIte, GameForm.instShortStar, IsEnd_zero]
  by_cases h3 : IsEnd .left g <;> simp [h3, reduceIte]
    <;> by_cases h4 : IsEnd .right g
    <;> rw [short_def]
    <;> intro p
    <;> cases p
  any_goals change (GameForm.moves _ _).Finite ∧ ∀ y ∈ GameForm.moves _ _, Short y
  any_goals simp only [Player.cases, Set.finite_singleton, Set.mem_range, Set.mem_singleton_iff,
                       Short.zero, Subtype.exists, and_imp, and_self, exists_prop,
                       forall_apply_eq_imp_iff₂, forall_eq, forall_exists_index, moves_ofSets, h3, h4,
                       reduceIte, and_false]
  all_goals constructor
  any_goals
    simp [star]
  any_goals
    have : Finite (Form.moves .right g) := Short.finite_moves .right g
    exact Set.finite_range (fun gr : Form.moves .right g => Adjoint (gr : G))
  any_goals
    have : Finite (Form.moves .left g) := Short.finite_moves .left g
    exact Set.finite_range (fun gl : Form.moves .left g => Adjoint (gl : G))
  all_goals
    intro gr h5
    have _ : Short gr := Short.of_mem_moves h5
    exact short_adjoint gr
termination_by g
decreasing_by all_goals form_wf

end Adjoint
end GameForm
