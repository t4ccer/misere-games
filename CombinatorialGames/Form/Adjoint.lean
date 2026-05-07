module

public import CombinatorialGames.Form.Short

universe u

public section

namespace Form

open Classical in
@[expose] noncomputable def Adjoint {G : Type (u + 1)} [Form G] (g : G) : G :=
  have := moves_small.{u} .left g
  have := moves_small.{u} .right g
  if IsEnd .left g ∧ IsEnd .right g then !{{0} | {0}}
  else if IsEnd .left g then !{Set.range fun gr : moves .right g => Adjoint (gr : G) | {0}}
  else if IsEnd .right g then !{{0} | Set.range fun gl : moves .left g => Adjoint (gl : G)}
  else !{ Set.range fun gr : moves .right g => Adjoint (gr : G)
        | Set.range fun gl : moves .left g => Adjoint (gl : G)}
termination_by g
decreasing_by form_wf

notation g"°" => Adjoint g

namespace Adjoint

variable {G : Type (u + 1)} [Form G]

@[simp]
theorem adjoint_zero_eq_star : ((0 : G)°) = !{{0} | {0}} := by
  unfold Adjoint
  simp only [IsEnd_zero, and_self, ↓reduceIte]

theorem adjoint_not_end (g : G) (p : Player) : ¬(IsEnd p (g°)) := by
  unfold Adjoint
  simp only [IsEnd_def]
  by_cases h1 : moves .left g = ∅ ∧ moves .right g = ∅ <;> simp [h1, IsEnd_def]
  all_goals by_cases h2 : moves .left g = ∅ <;> cases p
  all_goals by_cases h3 : moves .right g = ∅ <;> simp [h2, h3, IsEnd_def]
  rw [not_and] at h1
  exact h1 h2 h3

theorem adjoint_not_EndLike (g : G) (p : Player) : ¬(IsEndLike p (g°)) := by
  unfold Adjoint
  simp only [IsEnd_def]
  by_cases h1 : moves .left g = ∅ ∧ moves .right g = ∅ <;> simp [h1, IsEnd_def]
  all_goals by_cases h2 : moves .left g = ∅ <;> cases p
  all_goals by_cases h3 : moves .right g = ∅ <;> simp [h2, h3, IsEnd_def]
  rw [not_and] at h1
  exact h1 h2 h3

private theorem mem_leftMoves_mem_adjoint_rightMoves {g gl : G} (h1 : gl ∈ moves .left g) :
    gl° ∈ moves .right (g°) := by
  rw [Adjoint, IsEnd_def, IsEnd_def]
  have h2 : g ≠ 0 := mem_moves_ne_zero h1
  by_cases h3 : moves .left g = ∅ <;> by_cases h4 : moves .right g = ∅ <;> simp [*]
  · simp [h3] at h1
  · simp [h3] at h1
  · use gl
  · use gl

private theorem mem_rightMoves_mem_adjoint_leftMoves {g gr : G} (h1 : gr ∈ moves .right g) :
    gr° ∈ moves .left (g°) := by
  rw [Adjoint, IsEnd_def, IsEnd_def]
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

theorem mem_adjoint_end_opposite {g gp : G} {p : Player}
    (h1 : gp ∈ moves p (g°)) (h2 : IsEnd (-p) g) : gp = 0 := by
  unfold Adjoint at h1
  by_cases h3 : IsEnd p g
  · cases p
    all_goals
    · simp only [Player.neg_left, Player.neg_right] at h2
      simp only [h2, h3, and_self, ↓reduceIte, moves_ofSets, Player.cases,
        Set.mem_singleton_iff] at h1
      exact h1
  · have h4 : g ≠ 0 := not_IsEnd_ne_zero h3
    cases p
    all_goals
    · simp only [Player.neg_left, Player.neg_right] at h2
      simp only [h2, h3, and_true, and_false, ↓reduceIte, moves_ofSets, Player.cases,
        Set.mem_singleton_iff] at h1
      exact h1

private instance short_zero : Short (0 : G) := by
  rw [short_def]
  intro p
  simp

private theorem short_ofSets {s t : Set G} [Small s] [Small t]
    (hs_fin : s.Finite) (hs_short : ∀ g ∈ s, Short g)
    (ht_fin : t.Finite) (ht_short : ∀ g ∈ t, Short g) :
    Short !{s | t} := by
  rw [short_def]
  intro p
  cases p
  · exact ⟨by simpa using hs_fin, by simpa using hs_short⟩
  · exact ⟨by simpa using ht_fin, by simpa using ht_short⟩

private instance short_star : Short (!{{0} | {0}} : G) := by
  apply short_ofSets
  · simp
  · intro g hg
    simp only [Set.mem_singleton_iff] at hg
    subst g
    exact short_zero
  · simp
  · intro g hg
    simp only [Set.mem_singleton_iff] at hg
    subst g
    exact short_zero

instance short_adjoint (g : G) [h1 : Short g] : Short (g°) := by
  unfold Adjoint
  by_cases hleft : IsEnd .left g
  · by_cases hright : IsEnd .right g
    · simp [hleft, hright]
      exact short_star
    · simp [hleft, hright]
      apply short_ofSets
      · have : Finite (moves .right g) := Short.finite_moves .right g
        exact Set.finite_range (fun gr : moves .right g => Adjoint (gr : G))
      · intro gr hgr
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgr
        obtain ⟨gr', hgr', rfl⟩ := hgr
        haveI : Short gr' := Short.of_mem_moves hgr'
        exact short_adjoint gr'
      · simp
      · intro gr hgr
        simp only [Set.mem_singleton_iff] at hgr
        subst gr
        exact short_zero
  · by_cases hright : IsEnd .right g
    · simp [hleft, hright]
      apply short_ofSets
      · simp
      · intro gl hgl
        simp only [Set.mem_singleton_iff] at hgl
        subst gl
        exact short_zero
      · have : Finite (moves .left g) := Short.finite_moves .left g
        exact Set.finite_range (fun gl : moves .left g => Adjoint (gl : G))
      · intro gl hgl
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgl
        obtain ⟨gl', hgl', rfl⟩ := hgl
        haveI : Short gl' := Short.of_mem_moves hgl'
        exact short_adjoint gl'
    · simp [hleft, hright]
      apply short_ofSets
      · have : Finite (moves .right g) := Short.finite_moves .right g
        exact Set.finite_range (fun gr : moves .right g => Adjoint (gr : G))
      · intro gr hgr
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgr
        obtain ⟨gr', hgr', rfl⟩ := hgr
        haveI : Short gr' := Short.of_mem_moves hgr'
        exact short_adjoint gr'
      · have : Finite (moves .left g) := Short.finite_moves .left g
        exact Set.finite_range (fun gl : moves .left g => Adjoint (gl : G))
      · intro gl hgl
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgl
        obtain ⟨gl', hgl', rfl⟩ := hgl
        haveI : Short gl' := Short.of_mem_moves hgl'
        exact short_adjoint gl'
termination_by g
decreasing_by all_goals form_wf

end Adjoint

end Form
