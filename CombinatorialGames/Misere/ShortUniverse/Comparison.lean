module

public import CombinatorialGames.Misere.Separation
public import CombinatorialGames.Misere.Universe

universe u

variable {G : Type (u + 1)} [Form G]

open Form

public section

namespace Form

theorem ShortUniverse.adjoint_mem_of_short {U : G → Prop} [ShortUniverse U]
    (g : G) [Short g] : U (g°) := by
  unfold Adjoint
  by_cases hleft : IsEnd .left g
  · by_cases hright : IsEnd .right g
    · simp [hleft, hright]
      apply ClosedUnderDicoticShort.closed_dicotic_short
      · intro b hb
        simp only [Set.mem_singleton_iff] at hb
        rw [hb]
        exact ShortUniverse.zero_mem
      · intro c hc
        simp only [Set.mem_singleton_iff] at hc
        rw [hc]
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
        simp only [Set.mem_singleton_iff] at hc
        rw [hc]
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
        simp only [Set.mem_singleton_iff] at hb
        rw [hb]
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
        haveI : Short (hr : G) := Short.of_mem_moves hr.2
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
    · haveI : Short (gr : G) := Short.of_mem_moves gr.2
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
    · haveI : Short (hl : G) := Short.of_mem_moves hl.2
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

instance ShortUniverse.instComparisonSet {U : G → Prop} [ShortUniverse U] :
    Separation.ComparisonSet U where
  legal := Short
  legal_moves hg hmove := Short.of_mem_moves hmove
  legal_neg _ := inferInstance
  rightSeparatorCandidate_mem hh hx := by
    haveI : Short _ := hh
    exact rightSeparatorCandidate_mem_shortUniverse hx
  downlinkWitness_mem hg hh hxU hyU := by
    haveI : Short _ := hg
    haveI : Short _ := hh
    exact downlinkWitness_mem_shortUniverse hxU hyU

theorem rightSeparating_of_leftSeparating
    {U : G → Prop} [ShortUniverse U] {g h : G}
    [Short g] [Short h]
    (h_left_sep : LeftSeparating U g h) :
    RightSeparating U g h := by
  exact Separation.ComparisonSet.rightSeparating_of_leftSeparating
    (U := U) inferInstance h_left_sep

theorem leftSeparating_of_rightSeparating_of_not_misere_ge
    {U : G → Prop} [ShortUniverse U] {g h : G}
    [Short g] [Short h]
    (h_not_ge : ¬(g ≥m U h))
    (h_right_sep : RightSeparating U g h) :
    LeftSeparating U g h := by
  exact Separation.ComparisonSet.leftSeparating_of_rightSeparating_of_not_misere_ge
    (U := U) inferInstance h_not_ge h_right_sep

theorem left_and_right_separating_of_not_misere_ge {U : G → Prop} [ShortUniverse U]
    {g h : G} [Short g] [Short h]
    (h_not_ge : ¬(g ≥m U h)) :
    LeftSeparating U g h ∧ RightSeparating U g h := by
  exact Separation.ComparisonSet.left_and_right_separating_of_not_misere_ge
    (U := U) inferInstance inferInstance h_not_ge

theorem downlinked_of_not_exists_left_right_misere_ge {U : G → Prop} [ShortUniverse U]
    {g h : G} [Short g] [Short h]
    (h_left : ¬∃ gl ∈ moves .left g, gl ≥m U h)
    (h_right : ¬∃ hr ∈ moves .right h, g ≥m U hr) :
    Downlinked U g h := by
  exact Separation.ComparisonSet.downlinked_of_not_exists_left_right_misere_ge
    (U := U) inferInstance inferInstance h_left h_right

theorem misere_ge_imp_maintenance_right {U : G → Prop} [ShortUniverse U]
    {g h : G} [Short g] [Short h] (hge : g ≥m U h) :
    Maintenance U g h .right := by
  exact Separation.ComparisonSet.misere_ge_imp_maintenance_right
    (U := U) inferInstance inferInstance hge

theorem misere_ge_imp_maintenance_left {U : G → Prop} [ShortUniverse U]
    {g h : G} [Short g] [Short h] (hge : g ≥m U h) :
    Maintenance U g h .left := by
  exact Separation.ComparisonSet.misere_ge_imp_maintenance_left
    (U := U) inferInstance inferInstance hge

theorem misere_ge_imp_maintenance_and_proviso {U : G → Prop} [ShortUniverse U]
    (g h : G) [Short g] [Short h] :
    g ≥m U h →
      Maintenance U g h .right ∧ Maintenance U g h .left ∧
      Proviso U g h .right ∧ Proviso U h g .left := by
  intro hge
  exact Separation.ComparisonSet.misere_ge_imp_maintenance_and_proviso
    (U := U) inferInstance inferInstance hge

end Form
