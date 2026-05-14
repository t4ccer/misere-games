/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
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
  unfold adjoint
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
      · obtain ⟨gr, hgr⟩ := not_isEnd_exists_move hright
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
      · obtain ⟨gl, hgl⟩ := not_isEnd_exists_move hleft
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
      · obtain ⟨gr, hgr⟩ := not_isEnd_exists_move hright
        exact ⟨gr°, ⟨⟨gr, hgr⟩, rfl⟩⟩
      · obtain ⟨gl, hgl⟩ := not_isEnd_exists_move hleft
        exact ⟨gl°, ⟨⟨gl, hgl⟩, rfl⟩⟩
termination_by g
decreasing_by all_goals form_wf

private theorem rightSeparatorCandidate_mem {U : G → Prop} [Universe U]
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

private theorem downlinkWitness_mem {U : G → Prop} [Universe U]
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
    simp only [L, Separation.downlinkLeftSet, Separation.downlinkOptions,
      Separation.downlinkZero, Set.mem_union, Set.mem_range] at ha
    rcases ha with (⟨hr, rfl⟩ | ⟨gr, rfl⟩) | ha0
    · exact hyU hr
    · exact adjoint_mem (gr : G)
    · by_cases hz : IsEnd .right g ∧ IsEnd .right h
      · simp [hz] at ha0
        rw [ha0]
        exact Universe.zero_mem
      · simp [hz] at ha0
  · intro a ha
    simp only [R, Separation.downlinkRightSet, Separation.downlinkOptions,
      Separation.downlinkZero, Set.mem_union, Set.mem_range] at ha
    rcases ha with (⟨gl, rfl⟩ | ⟨hl, rfl⟩) | ha0
    · exact hxU gl
    · exact adjoint_mem (hl : G)
    · by_cases hz : IsEnd .left h ∧ IsEnd .left g
      · simp [hz] at ha0
        rw [ha0]
        exact Universe.zero_mem
      · simp [hz] at ha0
  · exact Separation.downlinkOptions_nonempty .left g h y
  · exact Separation.downlinkOptions_nonempty .right h g x

instance {U : G → Prop} [Universe U] : Separation.ComparisonSet U where
  Legal := fun _ => True
  legal_moves _ _ := trivial
  legal_neg _ := trivial
  rightSeparatorCandidate_mem _ hx := private rightSeparatorCandidate_mem hx
  downlinkWitness_mem _ _ hxU hyU := private downlinkWitness_mem hxU hyU

end Universe

end Form
