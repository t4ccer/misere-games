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

namespace ShortUniverse

variable {U : G → Prop} [ShortUniverse U]

private lemma rightSeparatorLeftSet_finite {h : G} (hh : IsShort h) :
    (Separation.rightSeparatorLeftSet h).Finite := by
  have := Short.finite_moves' Player.right hh
  exact (Set.finite_singleton (0 : G)).union
    (Set.finite_range (fun hr : moves .right h => (hr : G)°))

private lemma rightSeparatorLeftSet_short {h : G} (hh : IsShort h) :
    ∀ y ∈ Separation.rightSeparatorLeftSet h, IsShort y := by
  intro y hy
  simp only [Separation.rightSeparatorLeftSet, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_range] at hy
  rcases hy with rfl | ⟨hr, rfl⟩
  · exact Short.zero
  · exact Adjoint.short_adjoint (Short.of_mem_moves hh hr.prop)

private lemma downlinkZero_finite (p : Player) (g h : G) :
    (Separation.downlinkZero p g h).Finite := by
  unfold Separation.downlinkZero
  by_cases hz : IsEnd (-p) g ∧ IsEnd (-p) h <;> simp [hz]

private lemma downlinkOptions_finite {p : Player} {g h : G}
    (hg : IsShort g) (hh : IsShort h) (z : moves (-p) h → G) :
    (Separation.downlinkOptions p g h z).Finite := by
  have := Short.finite_moves' (-p) hg
  have := Short.finite_moves' (-p) hh
  exact ((Set.finite_range z).union
    (Set.finite_range (fun gp : moves (-p) g => (gp : G)°))).union
    (downlinkZero_finite p g h)

private lemma downlinkOptions_short {p : Player} {g h : G} {z : moves (-p) h → G}
    (hg : IsShort g) (hz : ∀ hp, IsShort (z hp)) :
    ∀ a ∈ Separation.downlinkOptions p g h z, IsShort a := by
  intro a ha
  simp [Separation.downlinkOptions, Separation.downlinkZero] at ha
  rcases ha with (⟨hp, hhp, rfl⟩ | ⟨gp, hgp, rfl⟩) | ha0
  · exact hz ⟨hp, hhp⟩
  · exact Adjoint.short_adjoint (Short.of_mem_moves hg hgp)
  · by_cases hend : IsEnd (-p) g ∧ IsEnd (-p) h
    · simp [ha0]
    · simp [hend] at ha0

instance : Separation.ComparisonSet.UniverseAdapter IsShort U where
  toUniverse := inferInstance
  isAmbient_hereditary := { has_option h_g hmove := Short.isOption h_g hmove }
  isAmbient_closed_neg := inferInstance
  isAmbient_adjoint := Adjoint.short_adjoint
  isAmbient_rightSeparatorCandidate := fun {h x} h_h h_x => by
    unfold Separation.rightSeparatorCandidate
    apply Short.ofSets
    · exact rightSeparatorLeftSet_finite h_h
    · exact rightSeparatorLeftSet_short h_h
    · exact Set.finite_singleton x
    · intro y hy
      rwa [Set.mem_singleton_iff.mp hy]
  isAmbient_downlinkWitness := by
    intro g h x y _ _ h_g h_h hx hy
    let L : Set G := Separation.downlinkLeftSet g h y
    let R : Set G := Separation.downlinkRightSet g h x
    change IsShort !{L | R}
    apply Short.ofSets
    · exact downlinkOptions_finite (p := .left) h_g h_h y
    · exact downlinkOptions_short (p := .left) h_g hy
    · exact downlinkOptions_finite (p := .right) h_h h_g x
    · exact downlinkOptions_short (p := .right) h_h hx

end ShortUniverse

end Form
