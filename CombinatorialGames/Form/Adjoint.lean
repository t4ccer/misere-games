/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import CombinatorialGames.Form.Short

universe u

public section

namespace Form

open Classical in
@[expose] noncomputable def adjoint {G : Type (u + 1)} [Form G] (g : G) : G :=
  have := moves_small.{u} .left g
  have := moves_small.{u} .right g
  if IsEnd .left g ∧ IsEnd .right g then !{{0} | {0}}
  else if IsEnd .left g then !{Set.range fun gr : moves .right g => adjoint (gr : G) | {0}}
  else if IsEnd .right g then !{{0} | Set.range fun gl : moves .left g => adjoint (gl : G)}
  else !{ Set.range fun gr : moves .right g => adjoint (gr : G)
        | Set.range fun gl : moves .left g => adjoint (gl : G)}
termination_by g
decreasing_by form_wf

notation g"°" => adjoint g

namespace Adjoint

variable {G : Type (u + 1)} [Form G]

@[simp]
theorem adjoint_zero_eq_star : ((0 : G)°) = !{{0} | {0}} := by
  unfold adjoint
  simp only [isEnd_zero, and_self, ↓reduceIte]

theorem adjoint_not_isEnd (g : G) (p : Player) : ¬(IsEnd p (g°)) := by
  unfold adjoint
  simp only [isEnd_def]
  by_cases h1 : moves .left g = ∅ ∧ moves .right g = ∅ <;> simp [h1, isEnd_def]
  all_goals by_cases h2 : moves .left g = ∅ <;> cases p
  all_goals by_cases h3 : moves .right g = ∅ <;> simp [h2, h3, isEnd_def]
  rw [not_and] at h1
  exact h1 h2 h3

theorem adjoint_not_isEndLike (g : G) (p : Player) : ¬(IsEndLike p (g°)) := by
  unfold adjoint
  simp only [isEnd_def]
  by_cases h1 : moves .left g = ∅ ∧ moves .right g = ∅ <;> simp [h1, isEnd_def]
  all_goals by_cases h2 : moves .left g = ∅ <;> cases p
  all_goals by_cases h3 : moves .right g = ∅ <;> simp [h2, h3, isEnd_def]
  rw [not_and] at h1
  exact h1 h2 h3

private theorem mem_leftMoves_mem_adjoint_rightMoves {g gl : G} (h1 : gl ∈ moves .left g) :
    gl° ∈ moves .right (g°) := by
  rw [adjoint, isEnd_def, isEnd_def]
  have h2 : g ≠ 0 := mem_moves_ne_zero h1
  by_cases h3 : moves .left g = ∅ <;> by_cases h4 : moves .right g = ∅ <;> simp [*]
  · simp [h3] at h1
  · simp [h3] at h1
  · use gl
  · use gl

private theorem mem_rightMoves_mem_adjoint_leftMoves {g gr : G} (h1 : gr ∈ moves .right g) :
    gr° ∈ moves .left (g°) := by
  rw [adjoint, isEnd_def, isEnd_def]
  have h2 : g ≠ 0 := mem_moves_ne_zero h1
  by_cases h3 : moves .left g = ∅ <;> by_cases h4 : moves .right g = ∅ <;> simp [*]
  · simp [h4] at h1
  · use gr
  · simp [h4] at h1
  · use gr

theorem mem_adjoint_mem_opposite {g gp : G} {p : Player}
    (h1 : gp ∈ moves p g) : gp° ∈ moves (-p) (g°) := by
  cases p
  · exact mem_leftMoves_mem_adjoint_rightMoves h1
  · exact mem_rightMoves_mem_adjoint_leftMoves h1

theorem mem_adjoint_exists_opposite {g gp : G} {p : Player} (h1 : gp ∈ moves p (g°))
    (h2 : ¬(IsEnd (-p) g)) : ∃ gnp ∈ moves (-p) g, gp = gnp° := by
  unfold adjoint at h1
  have h3 : g ≠ 0 := not_isEnd_ne_zero h2
  by_cases h4 : IsEnd p g <;> cases p
  any_goals rw [Player.neg_left] at h2
  any_goals rw [Player.neg_right] at h2
  all_goals
  · simp only [h4, h2, and_false, false_and, ↓reduceIte, moves_ofSets, Player.cases,
               Set.mem_range, Subtype.exists, exists_prop] at h1
    obtain ⟨gnp, h5, h6⟩ := h1
    use gnp
    exact And.symm ⟨Eq.symm h6, h5⟩

theorem mem_adjoint_end_opposite {g gp : G} {p : Player}
    (h1 : gp ∈ moves p (g°)) (h2 : IsEnd (-p) g) : gp = 0 := by
  unfold adjoint at h1
  by_cases h3 : IsEnd p g
  · cases p
    all_goals
    · simp only [Player.neg_left, Player.neg_right] at h2
      simp only [h2, h3, and_self, ↓reduceIte, moves_ofSets, Player.cases,
        Set.mem_singleton_iff] at h1
      exact h1
  · have h4 : g ≠ 0 := not_isEnd_ne_zero h3
    cases p
    all_goals
    · simp only [Player.neg_left, Player.neg_right] at h2
      simp only [h2, h3, and_true, and_false, ↓reduceIte, moves_ofSets, Player.cases,
        Set.mem_singleton_iff] at h1
      exact h1

theorem short_adjoint {g : G} (h1 : IsShort g) : IsShort (g°) := by
  unfold adjoint
  by_cases hleft : IsEnd .left g
  · by_cases hright : IsEnd .right g
    · simp only [hleft, hright, and_self, ↓reduceIte, Short.star]
    · simp only [hleft, hright, and_false, ↓reduceIte]
      apply Short.ofSets
      · have : Finite (moves .right g) := Short.finite_moves .right h1
        exact Set.finite_range (fun gr : moves .right g => adjoint (gr : G))
      · intro gr hgr
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgr
        obtain ⟨gr', hgr', rfl⟩ := hgr
        exact short_adjoint (Short.of_mem_moves h1 hgr')
      · exact Set.finite_singleton 0
      · intro gr hgr
        simp only [Set.mem_singleton_iff] at hgr
        subst gr
        exact Short.zero
  · by_cases hright : IsEnd .right g
    · simp only [hleft, hright, and_true, ↓reduceIte]
      apply Short.ofSets
      · exact Set.finite_singleton 0
      · intro gl hgl
        simp only [Set.mem_singleton_iff] at hgl
        subst gl
        exact Short.zero
      · have : Finite (moves .left g) := Short.finite_moves .left h1
        exact Set.finite_range (fun gl : moves .left g => adjoint (gl : G))
      · intro gl hgl
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgl
        obtain ⟨gl', hgl', rfl⟩ := hgl
        exact short_adjoint (Short.of_mem_moves h1 hgl')
    · simp only [hleft, hright, and_self, ↓reduceIte]
      apply Short.ofSets
      · have : Finite (moves .right g) := Short.finite_moves .right h1
        exact Set.finite_range (fun gr : moves .right g => adjoint (gr : G))
      · intro gr hgr
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgr
        obtain ⟨gr', hgr', rfl⟩ := hgr
        exact short_adjoint (Short.of_mem_moves h1 hgr')
      · have : Finite (moves .left g) := Short.finite_moves .left h1
        exact Set.finite_range (fun gl : moves .left g => adjoint (gl : G))
      · intro gl hgl
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgl
        obtain ⟨gl', hgl', rfl⟩ := hgl
        exact short_adjoint (Short.of_mem_moves h1 hgl')
termination_by g
decreasing_by all_goals form_wf

end Adjoint

end Form
