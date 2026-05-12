module

public import CombinatorialGames.Misere.Separation
public import CombinatorialGames.Misere.Universe

universe u

variable {G : Type (u + 1)} [Form G]

open Form

public section

namespace Form

theorem ShortUniverse.adjoint_mem_of_short {U : G → Prop} [ShortUniverse U] {g : G} (h_g : IsShort g)
    : U (g°) := by
  unfold adjoint
  by_cases hleft : IsEnd .left g
  · by_cases hright : IsEnd .right g
    · simp [hleft, hright]
      apply ClosedUnderDicoticShort.closed_dicotic_short
      · intro b hb
        rw [Set.mem_singleton_iff.mp hb]
        exact ShortUniverse.zero_mem
      · intro c hc
        rw [Set.mem_singleton_iff.mp hc]
        exact ShortUniverse.zero_mem
      · exact Set.finite_singleton 0
      · exact Set.singleton_nonempty 0
      · exact Set.finite_singleton 0
      · exact Set.singleton_nonempty 0
    · simp [hleft, hright]
      apply ClosedUnderDicoticShort.closed_dicotic_short
      · intro b hb
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hb
        obtain ⟨gr, hgr, rfl⟩ := hb
        exact ShortUniverse.adjoint_mem_of_short (Short.of_mem_moves h_g hgr)
      · intro c hc
        rw [Set.mem_singleton_iff.mp hc]
        exact ShortUniverse.zero_mem
      · have : Finite (moves .right g) := Short.finite_moves .right h_g
        exact Set.finite_range (fun gr : moves .right g => (gr : G)°)
      · obtain ⟨gr, hgr⟩ := not_isEnd_exists_move hright
        exact ⟨gr°, ⟨⟨gr, hgr⟩, rfl⟩⟩
      · exact Set.finite_singleton 0
      · exact Set.singleton_nonempty 0
  · by_cases hright : IsEnd .right g
    · simp [hleft, hright]
      apply ClosedUnderDicoticShort.closed_dicotic_short
      · intro b hb
        rw [Set.mem_singleton_iff.mp hb]
        exact ShortUniverse.zero_mem
      · intro c hc
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hc
        obtain ⟨gl, hgl, rfl⟩ := hc
        exact ShortUniverse.adjoint_mem_of_short (Short.of_mem_moves h_g hgl)
      · exact Set.finite_singleton 0
      · exact Set.singleton_nonempty 0
      · have : Finite (moves .left g) := Short.finite_moves .left h_g
        exact Set.finite_range (fun gl : moves .left g => (gl : G)°)
      · obtain ⟨gl, hgl⟩ := not_isEnd_exists_move hleft
        exact ⟨gl°, ⟨⟨gl, hgl⟩, rfl⟩⟩
    · simp [hleft, hright]
      apply ClosedUnderDicoticShort.closed_dicotic_short
      · intro b hb
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hb
        obtain ⟨gr, hgr, rfl⟩ := hb
        exact ShortUniverse.adjoint_mem_of_short (Short.of_mem_moves h_g hgr)
      · intro c hc
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hc
        obtain ⟨gl, hgl, rfl⟩ := hc
        exact ShortUniverse.adjoint_mem_of_short (Short.of_mem_moves h_g hgl)
      · have : Finite (moves .right g) := Short.finite_moves .right h_g
        exact Set.finite_range (fun gr : moves .right g => (gr : G)°)
      · obtain ⟨gr, hgr⟩ := not_isEnd_exists_move hright
        exact ⟨gr°, ⟨⟨gr, hgr⟩, rfl⟩⟩
      · have : Finite (moves .left g) := Short.finite_moves .left h_g
        exact Set.finite_range (fun gl : moves .left g => (gl : G)°)
      · obtain ⟨gl, hgl⟩ := not_isEnd_exists_move hleft
        exact ⟨gl°, ⟨⟨gl, hgl⟩, rfl⟩⟩
termination_by g
decreasing_by all_goals form_wf

private theorem rightSeparatorCandidate_mem_shortUniverse {U : G → Prop} [ShortUniverse U]
    {h x : G} (h_h : IsShort h) (hx : U x) :
    U (Separation.rightSeparatorCandidate h x) := by
  unfold Separation.rightSeparatorCandidate
  apply ClosedUnderDicoticShort.closed_dicotic_short
  · intro b hb
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hb
    cases hb with
    | inl hb_zero =>
        rw [hb_zero]
        exact ShortUniverse.zero_mem
    | inr hb_adjoint =>
        obtain ⟨hr, rfl⟩ := hb_adjoint
        exact ShortUniverse.adjoint_mem_of_short (Short.of_mem_moves h_h hr.prop)
  · intro c hc
    simp only [Set.mem_singleton_iff] at hc
    rwa [hc]
  · have := Short.finite_moves' Player.right h_h
    exact (Set.finite_singleton (0 : G)).union
      (Set.finite_range (fun hr : moves .right h => (hr : G)°))
  · exact ⟨0, Or.inl rfl⟩
  · exact Set.finite_singleton x
  · exact Set.singleton_nonempty x

private theorem downlinkWitness_mem_shortUniverse {U : G → Prop} [ShortUniverse U]
    {g h : G} (h_g : IsShort g) (h_h : IsShort h)
    {x : moves .left g → G} {y : moves .right h → G}
    [Small (Separation.downlinkLeftSet g h y)]
    [Small (Separation.downlinkRightSet g h x)]
    (hxU : ∀ gl, U (x gl)) (hyU : ∀ hr, U (y hr)) :
    U (Separation.downlinkWitness g h x y) := by
  let L : Set G := Separation.downlinkLeftSet g h y
  let R : Set G := Separation.downlinkRightSet g h x
  have := Short.finite_moves' Player.right h_h
  have := Short.finite_moves' Player.left h_h
  have := Short.finite_moves' Player.right h_g
  have := Short.finite_moves' Player.left h_g
  have hLfin : L.Finite := by
    exact ((Set.finite_range y).union
      (Set.finite_range (fun gr : moves .right g => (gr : G)°))).union
      (by
        unfold Separation.downlinkZeroLeft
        by_cases hz : IsEnd .right g ∧ IsEnd .right h <;> simp [hz])
  have hRfin : R.Finite := by
    exact ((Set.finite_range x).union
      (Set.finite_range (fun hl : moves .left h => (hl : G)°))).union
      (by
        unfold Separation.downlinkZeroRight
        by_cases hz : IsEnd .left g ∧ IsEnd .left h <;> simp [hz])
  change U !{L | R}
  apply ClosedUnderDicoticShort.closed_dicotic_short
  · intro a ha
    simp only [L, Separation.downlinkLeftSet, Separation.downlinkZeroLeft,
      Set.mem_union, Set.mem_range] at ha
    rcases ha with (⟨hr, rfl⟩ | ⟨gr, rfl⟩) | ha0
    · exact hyU hr
    · exact ShortUniverse.adjoint_mem_of_short (Short.of_mem_moves h_g gr.prop)
    · by_cases hz : IsEnd .right g ∧ IsEnd .right h
      · simp [hz] at ha0
        rw [ha0]
        exact ShortUniverse.zero_mem
      · simp [hz] at ha0
  · intro a ha
    simp only [R, Separation.downlinkRightSet, Separation.downlinkZeroRight,
      Set.mem_union, Set.mem_range] at ha
    rcases ha with (⟨gl, rfl⟩ | ⟨hl, rfl⟩) | ha0
    · exact hxU gl
    · exact ShortUniverse.adjoint_mem_of_short (Short.of_mem_moves h_h hl.prop)
    · by_cases hz : IsEnd .left g ∧ IsEnd .left h
      · simp [hz] at ha0
        rw [ha0]
        exact ShortUniverse.zero_mem
      · simp [hz] at ha0
  · exact hLfin
  · exact Separation.downlinkLeftSet_nonempty g h y
  · exact hRfin
  · exact Separation.downlinkRightSet_nonempty g h x

instance {U : G → Prop} [ShortUniverse U] : Separation.ComparisonSet U where
  Legal := IsShort
  legal_moves h_g hmove := Short.of_mem_moves h_g hmove
  legal_neg h_g := Short.neg_iff.mpr h_g
  rightSeparatorCandidate_mem := private rightSeparatorCandidate_mem_shortUniverse
  downlinkWitness_mem h_g h_h hxU hyU := private downlinkWitness_mem_shortUniverse h_g h_h hxU hyU

end Form
