module

public import CombinatorialGames.Misere.Separation
public import CombinatorialGames.Misere.Universe

universe u

variable {G : Type (u + 1)} [Form G]

open Form

public section

namespace Form

namespace Universe

theorem adjoint_mem {U : G → Prop} [Universe U] (g : G) : U (g°) := by
  unfold Adjoint
  by_cases hleft : IsEnd .left g
  · by_cases hright : IsEnd .right g
    · simp [hleft, hright]
      apply ClosedUnderDicotic.closed_dicotic
      · intro b hb
        simp only [Set.mem_singleton_iff] at hb
        rw [hb]
        exact Universe.zero_mem
      · intro c hc
        simp only [Set.mem_singleton_iff] at hc
        rw [hc]
        exact Universe.zero_mem
      · exact Set.singleton_nonempty 0
      · exact Set.singleton_nonempty 0
    · simp [hleft, hright]
      apply ClosedUnderDicotic.closed_dicotic
      · intro b hb
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hb
        obtain ⟨gr, hgr, rfl⟩ := hb
        exact adjoint_mem gr
      · intro c hc
        simp only [Set.mem_singleton_iff] at hc
        rw [hc]
        exact Universe.zero_mem
      · obtain ⟨gr, hgr⟩ := not_IsEnd_exists_move hright
        exact ⟨gr°, ⟨⟨gr, hgr⟩, rfl⟩⟩
      · exact Set.singleton_nonempty 0
  · by_cases hright : IsEnd .right g
    · simp [hleft, hright]
      apply ClosedUnderDicotic.closed_dicotic
      · intro b hb
        simp only [Set.mem_singleton_iff] at hb
        rw [hb]
        exact Universe.zero_mem
      · intro c hc
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hc
        obtain ⟨gl, hgl, rfl⟩ := hc
        exact adjoint_mem gl
      · exact Set.singleton_nonempty 0
      · obtain ⟨gl, hgl⟩ := not_IsEnd_exists_move hleft
        exact ⟨gl°, ⟨⟨gl, hgl⟩, rfl⟩⟩
    · simp [hleft, hright]
      apply ClosedUnderDicotic.closed_dicotic
      · intro b hb
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hb
        obtain ⟨gr, hgr, rfl⟩ := hb
        exact adjoint_mem gr
      · intro c hc
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hc
        obtain ⟨gl, hgl, rfl⟩ := hc
        exact adjoint_mem gl
      · obtain ⟨gr, hgr⟩ := not_IsEnd_exists_move hright
        exact ⟨gr°, ⟨⟨gr, hgr⟩, rfl⟩⟩
      · obtain ⟨gl, hgl⟩ := not_IsEnd_exists_move hleft
        exact ⟨gl°, ⟨⟨gl, hgl⟩, rfl⟩⟩
termination_by g
decreasing_by all_goals form_wf

theorem rightSeparatorCandidate_mem {U : G → Prop} [Universe U]
    {h x : G} (hx : U x) : U (Separation.rightSeparatorCandidate h x) := by
  unfold Separation.rightSeparatorCandidate
  apply ClosedUnderDicotic.closed_dicotic
  · intro b hb
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hb
    cases hb with
    | inl hb_zero =>
        rw [hb_zero]
        exact Universe.zero_mem
    | inr hb_adjoint =>
        obtain ⟨hr, rfl⟩ := hb_adjoint
        exact adjoint_mem (hr : G)
  · intro c hc
    simp only [Set.mem_singleton_iff] at hc
    rwa [hc]
  · exact ⟨0, Or.inl rfl⟩
  · exact Set.singleton_nonempty x

theorem downlinkWitness_mem {U : G → Prop} [Universe U]
    {g h : G} {x : moves .left g → G} {y : moves .right h → G}
    [Small (Separation.downlinkLeftSet g h y)]
    [Small (Separation.downlinkRightSet g h x)]
    (hxU : ∀ gl, U (x gl)) (hyU : ∀ hr, U (y hr)) :
    U (Separation.downlinkWitness g h x y) := by
  let L : Set G := Separation.downlinkLeftSet g h y
  let R : Set G := Separation.downlinkRightSet g h x
  change U !{L | R}
  apply ClosedUnderDicotic.closed_dicotic
  · intro a ha
    simp only [L, Separation.downlinkLeftSet, Separation.downlinkZeroLeft,
      Set.mem_union, Set.mem_range] at ha
    rcases ha with (⟨hr, rfl⟩ | ⟨gr, rfl⟩) | ha0
    · exact hyU hr
    · exact adjoint_mem (gr : G)
    · by_cases hz : IsEnd .right g ∧ IsEnd .right h
      · simp [hz] at ha0
        rw [ha0]
        exact Universe.zero_mem
      · simp [hz] at ha0
  · intro a ha
    simp only [R, Separation.downlinkRightSet, Separation.downlinkZeroRight,
      Set.mem_union, Set.mem_range] at ha
    rcases ha with (⟨gl, rfl⟩ | ⟨hl, rfl⟩) | ha0
    · exact hxU gl
    · exact adjoint_mem (hl : G)
    · by_cases hz : IsEnd .left g ∧ IsEnd .left h
      · simp [hz] at ha0
        rw [ha0]
        exact Universe.zero_mem
      · simp [hz] at ha0
  · exact Separation.downlinkLeftSet_nonempty g h y
  · exact Separation.downlinkRightSet_nonempty g h x

instance instComparisonSet {U : G → Prop} [Universe U] :
    Separation.ComparisonSet U where
  legal := fun _ => True
  legal_moves _ _ := trivial
  legal_neg _ := trivial
  rightSeparatorCandidate_mem _ hx := rightSeparatorCandidate_mem hx
  downlinkWitness_mem _ _ hxU hyU := downlinkWitness_mem hxU hyU

theorem rightSeparating_of_leftSeparating
    {U : G → Prop} [Universe U] {g h : G}
    (h_left_sep : LeftSeparating U g h) :
    RightSeparating U g h := by
  exact Separation.ComparisonSet.rightSeparating_of_leftSeparating
    (U := U) trivial h_left_sep

theorem leftSeparating_of_rightSeparating_of_not_misere_ge
    {U : G → Prop} [Universe U] {g h : G}
    (h_not_ge : ¬(g ≥m U h))
    (h_right_sep : RightSeparating U g h) :
    LeftSeparating U g h := by
  exact Separation.ComparisonSet.leftSeparating_of_rightSeparating_of_not_misere_ge
    (U := U) trivial h_not_ge h_right_sep

theorem left_and_right_separating_of_not_misere_ge {U : G → Prop} [Universe U]
    {g h : G} (h_not_ge : ¬(g ≥m U h)) :
    LeftSeparating U g h ∧ RightSeparating U g h := by
  exact Separation.ComparisonSet.left_and_right_separating_of_not_misere_ge
    (U := U) trivial trivial h_not_ge

theorem downlinked_of_not_exists_left_right_misere_ge {U : G → Prop} [Universe U]
    {g h : G}
    (h_left : ¬∃ gl ∈ moves .left g, gl ≥m U h)
    (h_right : ¬∃ hr ∈ moves .right h, g ≥m U hr) :
    Downlinked U g h := by
  exact Separation.ComparisonSet.downlinked_of_not_exists_left_right_misere_ge
    (U := U) trivial trivial h_left h_right

theorem misere_ge_imp_maintenance_right {U : G → Prop} [Universe U]
    {g h : G} (hge : g ≥m U h) :
    Maintenance U g h .right := by
  exact Separation.ComparisonSet.misere_ge_imp_maintenance_right
    (U := U) trivial trivial hge

theorem misere_ge_imp_maintenance_left {U : G → Prop} [Universe U]
    {g h : G} (hge : g ≥m U h) :
    Maintenance U g h .left := by
  exact Separation.ComparisonSet.misere_ge_imp_maintenance_left
    (U := U) trivial trivial hge

theorem misere_ge_imp_maintenance_and_proviso {U : G → Prop} [Universe U]
    (g h : G) :
    g ≥m U h →
      Maintenance U g h .right ∧ Maintenance U g h .left ∧
      Proviso U g h .right ∧ Proviso U h g .left := by
  intro hge
  exact Separation.ComparisonSet.misere_ge_imp_maintenance_and_proviso
    (U := U) trivial trivial hge

end Universe

end Form
