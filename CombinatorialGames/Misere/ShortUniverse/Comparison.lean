module

public import CombinatorialGames.Misere.Separation
public import CombinatorialGames.Misere.Universe

universe u

variable {G : Type (u + 1)} [Form G]

open Form

public section

namespace Form

theorem ShortUniverse.adjoint_mem_of_short {U : G → Prop} [ShortUniverse U] (g : G) [Short g]
    : U (g°) := by
  unfold Adjoint
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
        haveI : Short gr := Short.of_mem_moves hgr
        exact ShortUniverse.adjoint_mem_of_short gr
      · intro c hc
        rw [Set.mem_singleton_iff.mp hc]
        exact ShortUniverse.zero_mem
      · have : Finite (moves .right g) := Short.finite_moves .right g
        exact Set.finite_range (fun gr : moves .right g => (gr : G)°)
      · obtain ⟨gr, hgr⟩ := not_IsEnd_exists_move hright
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
        haveI : Short gl := Short.of_mem_moves hgl
        exact ShortUniverse.adjoint_mem_of_short gl
      · exact Set.finite_singleton 0
      · exact Set.singleton_nonempty 0
      · have : Finite (moves .left g) := Short.finite_moves .left g
        exact Set.finite_range (fun gl : moves .left g => (gl : G)°)
      · obtain ⟨gl, hgl⟩ := not_IsEnd_exists_move hleft
        exact ⟨gl°, ⟨⟨gl, hgl⟩, rfl⟩⟩
    · simp [hleft, hright]
      apply ClosedUnderDicoticShort.closed_dicotic_short
      · intro b hb
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hb
        obtain ⟨gr, hgr, rfl⟩ := hb
        haveI : Short gr := Short.of_mem_moves hgr
        exact ShortUniverse.adjoint_mem_of_short gr
      · intro c hc
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hc
        obtain ⟨gl, hgl, rfl⟩ := hc
        haveI : Short gl := Short.of_mem_moves hgl
        exact ShortUniverse.adjoint_mem_of_short gl
      · have : Finite (moves .right g) := Short.finite_moves .right g
        exact Set.finite_range (fun gr : moves .right g => (gr : G)°)
      · obtain ⟨gr, hgr⟩ := not_IsEnd_exists_move hright
        exact ⟨gr°, ⟨⟨gr, hgr⟩, rfl⟩⟩
      · have : Finite (moves .left g) := Short.finite_moves .left g
        exact Set.finite_range (fun gl : moves .left g => (gl : G)°)
      · obtain ⟨gl, hgl⟩ := not_IsEnd_exists_move hleft
        exact ⟨gl°, ⟨⟨gl, hgl⟩, rfl⟩⟩
termination_by g
decreasing_by all_goals form_wf

private theorem rightSeparatorCandidate_mem_shortUniverse {U : G → Prop} [ShortUniverse U]
    {h x : G} [Short h] (hx : U x) :
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
        haveI : Short (hr : G) := Short.of_mem_moves hr.prop
        exact ShortUniverse.adjoint_mem_of_short (hr : G)
  · intro c hc
    simp only [Set.mem_singleton_iff] at hc
    rwa [hc]
  · exact (Set.finite_singleton (0 : G)).union
      (Set.finite_range (fun hr : moves .right h => (hr : G)°))
  · exact ⟨0, Or.inl rfl⟩
  · exact Set.finite_singleton x
  · exact Set.singleton_nonempty x

private theorem downlinkWitness_mem_shortUniverse {U : G → Prop} [ShortUniverse U]
    {g h : G} [Short g] [Short h]
    {x : moves .left g → G} {y : moves .right h → G}
    [Small (Separation.downlinkLeftSet g h y)]
    [Small (Separation.downlinkRightSet g h x)]
    (hxU : ∀ gl, U (x gl)) (hyU : ∀ hr, U (y hr)) :
    U (Separation.downlinkWitness g h x y) := by
  let L : Set G := Separation.downlinkLeftSet g h y
  let R : Set G := Separation.downlinkRightSet g h x
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
    · haveI : Short (gr : G) := Short.of_mem_moves gr.prop
      exact ShortUniverse.adjoint_mem_of_short (gr : G)
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
    · haveI : Short (hl : G) := Short.of_mem_moves hl.prop
      exact ShortUniverse.adjoint_mem_of_short (hl : G)
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
  Legal := Short
  legal_moves _ hmove := Short.of_mem_moves hmove
  legal_neg _ := inferInstance
  rightSeparatorCandidate_mem _ hx := private rightSeparatorCandidate_mem_shortUniverse hx
  downlinkWitness_mem _ _ hxU hyU := private downlinkWitness_mem_shortUniverse hxU hyU

end Form
