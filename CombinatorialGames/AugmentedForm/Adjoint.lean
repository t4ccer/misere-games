import CombinatorialGames.AugmentedForm
import CombinatorialGames.GameForm.Adjoint

namespace AugmentedForm.Adjoint

open Form

theorem mem_adjoint_end_opposite {g gp : AugmentedForm} {p : Player}
    (h1 : gp ∈ moves p (g° : AugmentedForm)) (h2 : IsEnd (-p) g) : gp = 0 := by
  have h0 : AugmentedForm.TombstoneFree gp := by
    have h0 : AugmentedForm.TombstoneFree (g°) := AugmentedForm.ofGameForm_tombstoneFree (g°)
    exact AugmentedForm.TombstoneFree.moves h0 p gp h1
  unfold GameForm.Adjoint at h1
  by_cases h3 : IsEnd p g
  · cases p
    all_goals
    · simp only [Player.neg_left, Player.neg_right] at h2
      simp only [h2, h3, and_self, ↓reduceIte] at h1
      obtain ⟨gp', h4, h5⟩ := mem_ofGameForm_exists_mem h0 h1
      simp only [GameForm.moves_star, Set.mem_singleton_iff] at h4
      rw [<-h5, h4]
      exact AugmentedForm.ofGameForm_zero
  · have h4 : g ≠ 0 := not_IsEnd_ne_zero h3
    cases p
    all_goals
    · simp only [Player.neg_left, Player.neg_right] at h2
      simp only [h2, h3, and_true, and_false, ↓reduceIte] at h1
      obtain ⟨gp', h4, h5⟩ := mem_ofGameForm_exists_mem h0 h1
      simp [Player.cases, Set.mem_singleton_iff] at h4
      rw [<-h5, h4]
      exact AugmentedForm.ofGameForm_zero

theorem mem_adjoint_exists_opposite {g gp : AugmentedForm} {p : Player}
    (h1 : gp ∈ moves p (g° : AugmentedForm)) (h2 : ¬(IsEnd (-p) g))
    : ∃ gnp ∈ moves (-p) g, gp = gnp° := by
  have h0 : AugmentedForm.TombstoneFree gp := by
    have h0 : AugmentedForm.TombstoneFree (g°) := AugmentedForm.ofGameForm_tombstoneFree (g°)
    exact AugmentedForm.TombstoneFree.moves h0 p gp h1
  unfold GameForm.Adjoint at h1
  have h3 : g ≠ 0 := not_IsEnd_ne_zero h2
  by_cases h4 : IsEnd p g <;> cases p
  any_goals rw [Player.neg_left] at h2
  any_goals rw [Player.neg_right] at h2
  all_goals
  · simp [h4, h2, and_false, ↓reduceIte] at h1
    have ⟨gp', h7, h8⟩ := mem_ofGameForm_exists_mem h0 h1
    simp only [GameForm.moves_ofSets, Player.cases, Set.mem_range, Subtype.exists, exists_prop] at h7
    obtain ⟨gpp, h9, h10⟩ := h7
    use gpp
    simp only [Player.neg_left, Player.neg_right, h9, h10, h8, true_and]

@[simp]
theorem adjoint_not_EndLike {g : AugmentedForm} {p : Player}
    : ¬EndLike p (ofGameForm (g°)) :=
  EndLike_ofGameForm_iff.not.mpr (GameForm.Adjoint.adjoint_not_end g p)

end AugmentedForm.Adjoint
