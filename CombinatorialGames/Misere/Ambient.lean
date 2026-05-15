/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/

module

public import CombinatorialGames.Misere.Separation

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Classical

public section

namespace Form

open Separation

class Ambient (IsAmbient : outParam (G → Prop)) extends Hereditary IsAmbient, ClosedUnderNeg IsAmbient where
  isAmbient_adjoint {g : G} : IsAmbient g → IsAmbient (g°)
  isAmbient_rightSeparatorCandidate {h x : G} :
    IsAmbient h → IsAmbient x → IsAmbient (rightSeparatorCandidate h x)
  isAmbient_downlinkWitness {g h : G} {x : moves .left g → G} {y : moves .right h → G}
    [Small (downlinkLeftSet g h y)] [Small (downlinkRightSet g h x)] :
    IsAmbient g → IsAmbient h → (∀ gl, IsAmbient (x gl)) → (∀ hr, IsAmbient (y hr)) →
      IsAmbient (downlinkWitness g h x y)

instance : Ambient (fun _ => True) (G := G) where
  isAmbient_adjoint _ := by
    trivial
  isAmbient_rightSeparatorCandidate _ _ := by
    trivial
  isAmbient_downlinkWitness _ _ _ _ := by
    trivial

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

instance : Ambient IsShort (G := G) where
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
