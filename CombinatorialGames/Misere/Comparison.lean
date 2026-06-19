/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import CombinatorialGames.Misere.Ambient
public import CombinatorialGames.Misere.Universe

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Form.Misere.Outcome
open Form.Misere.Adjoint
open Separation

public section

namespace Form

/-- A set `A` is *promain* (within the ambient `IsAmbient`) when comparison of
ambient forms modulo `A` is decided entirely by the maintenance and proviso
conditions. -/
@[expose] def Promain (IsAmbient A : G → Prop) : Prop :=
  ∀ ⦃g h : G⦄, IsAmbient g → IsAmbient h →
    (g ≥m A h ↔ Maintenance A g h .right ∧ Maintenance A g h .left ∧
               Proviso A g h .right ∧ Proviso A h g .left)

/--
This is an interface used to show that $G\ge_\mathcal{U}H$ implies
`Form.Maintenance` and `Form.Proviso` (see `maintenance_proviso_of_misereGE`).

The `IsAmbient` predicate dictates what game forms exist in the ambient space
for comparison. For example, in a `ShortUniverse`, `IsAmbient` is
`Form.IsShort`. We require the set of ambient forms to be `Form.Hereditary`.
-/
class ComparisonSet (IsAmbient : G → Prop) (A : G → Prop) extends Hereditary IsAmbient where
  separating_pair_of_not_misereGE {g h : G} :
    IsAmbient g → IsAmbient h → ¬(g ≥m A h) →
      LeftSeparating A g h ∧ RightSeparating A g h
  downlinked_of_separating {g h : G} :
    IsAmbient g → IsAmbient h →
    (∀ gl : moves .left g, LeftSeparating A (gl : G) h) →
    (∀ hr : moves .right h, RightSeparating A g (hr : G)) →
      Downlinked A g h

variable {IsAmbient A : G → Prop}

/-! ### Membership of the separating and downlinked constructions

These auxiliary forms are all dicotic, so they live in every `A` that contains
`0` and is dicotically closed. -/

section

variable [Ambient IsAmbient] [ClosedUnderDicotic IsAmbient A] {r : G}

/--
The rooted adjoint of an ambient form lies in any dicotically closed `A`
containing the root `r`.
-/
theorem rootedAdjoint_mem_of_isAmbient (h_root : A r) (h_sub : A ≤ IsAmbient)
    {g : G} (hg : IsAmbient g) :
    A (rootedAdjoint r g) := by
  have h_root_mem : ∀ a ∈ ({r} : Set G), A a := by
    intro a ha
    rw [Set.mem_singleton_iff.mp ha]
    exact h_root
  have h_root_nonempty : ({r} : Set G).Nonempty := Set.singleton_nonempty r
  have hAdjAmbient := Ambient.isAmbient_rootedAdjoint (h_sub r h_root) hg
  have hAdjRange : ∀ p, ∀ a ∈ Set.range (fun gp : moves p g => rootedAdjoint r (gp : G)), A a := by
    intro p a ha
    simp only [Set.mem_range, Subtype.exists, exists_prop] at ha
    obtain ⟨gp, hgp, rfl⟩ := ha
    exact rootedAdjoint_mem_of_isAmbient h_root h_sub
      (Hereditary.has_option hg (IsOption.of_mem_moves hgp))
  have hAdjRange_nonempty :
      ∀ {p}, ¬IsEnd p g → (Set.range fun gp : moves p g => rootedAdjoint r (gp : G)).Nonempty := by
    intro p hp
    obtain ⟨gp, hgp⟩ := not_isEnd_exists_move hp
    exact ⟨rootedAdjoint r gp, ⟨⟨gp, hgp⟩, rfl⟩⟩
  unfold rootedAdjoint
  by_cases hleft : IsEnd .left g
  · by_cases hright : IsEnd .right g
    · simp [hleft, hright]
      apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
      · exact h_root_mem
      · exact h_root_mem
      · exact h_root_nonempty
      · exact h_root_nonempty
      · unfold rootedAdjoint at hAdjAmbient
        simpa [hleft, hright] using hAdjAmbient
    · simp [hleft, hright]
      apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
      · exact hAdjRange .right
      · exact h_root_mem
      · exact hAdjRange_nonempty hright
      · exact h_root_nonempty
      · unfold rootedAdjoint at hAdjAmbient
        simpa [hleft, hright] using hAdjAmbient
  · by_cases hright : IsEnd .right g
    · simp [hleft, hright]
      apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
      · exact h_root_mem
      · exact hAdjRange .left
      · exact h_root_nonempty
      · exact hAdjRange_nonempty hleft
      · unfold rootedAdjoint at hAdjAmbient
        simpa [hleft, hright] using hAdjAmbient
    · simp [hleft, hright]
      apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
      · exact hAdjRange .right
      · exact hAdjRange .left
      · exact hAdjRange_nonempty hright
      · exact hAdjRange_nonempty hleft
      · unfold rootedAdjoint at hAdjAmbient
        simpa [hleft, hright] using hAdjAmbient
termination_by g
decreasing_by all_goals form_wf

private theorem rightSeparatorLeftSet_mem (h_root : A r) (h_sub : A ≤ IsAmbient)
    {h : G} (hh : IsAmbient h) :
    ∀ b ∈ rightSeparatorLeftSet r h, A b := by
  intro b hb
  simp only [rightSeparatorLeftSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hb
  rcases hb with rfl | ⟨hr, rfl⟩
  · exact h_root
  · exact rootedAdjoint_mem_of_isAmbient h_root h_sub
      (Hereditary.has_option hh (IsOption.of_mem_moves hr.prop))

private theorem rightSeparatorCandidate_mem (h_root : A r) (h_sub : A ≤ IsAmbient)
    {h x : G} (hh : IsAmbient h) (hx : A x) :
    A (rightSeparatorCandidate r h x) := by
  unfold rightSeparatorCandidate
  apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
  · exact rightSeparatorLeftSet_mem h_root h_sub hh
  · intro c hc
    rwa [Set.mem_singleton_iff.mp hc]
  · exact ⟨r, Or.inl rfl⟩
  · exact Set.singleton_nonempty x
  · exact Ambient.isAmbient_rightSeparatorCandidate (h_sub r h_root) hh (h_sub x hx)

private theorem leftSeparatorRightSet_mem (h_root : A r) (h_sub : A ≤ IsAmbient)
    {g : G} (hg : IsAmbient g) :
    ∀ b ∈ leftSeparatorRightSet r g, A b := by
  intro b hb
  simp only [leftSeparatorRightSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hb
  rcases hb with rfl | ⟨gl, rfl⟩
  · exact h_root
  · exact rootedAdjoint_mem_of_isAmbient h_root h_sub
      (Hereditary.has_option hg (IsOption.of_mem_moves gl.prop))

private theorem leftSeparatorCandidate_mem (h_root : A r) (h_sub : A ≤ IsAmbient)
    {g x : G} (hg : IsAmbient g) (hx : A x) :
    A (leftSeparatorCandidate r g x) := by
  unfold leftSeparatorCandidate
  apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
  · intro c hc
    rwa [Set.mem_singleton_iff.mp hc]
  · exact leftSeparatorRightSet_mem h_root h_sub hg
  · exact Set.singleton_nonempty x
  · exact ⟨r, Or.inl rfl⟩
  · exact Ambient.isAmbient_leftSeparatorCandidate (h_sub r h_root) hg (h_sub x hx)

private theorem downlinkOptions_mem (h_root : A r) (h_sub : A ≤ IsAmbient)
    {p : Player} {g h : G} {z : moves (-p) h → G}
    (hg : IsAmbient g) (hzA : ∀ hp, A (z hp)) :
    ∀ a ∈ downlinkOptions r p g h z, A a := by
  intro a ha
  simp [downlinkOptions, downlinkZero] at ha
  rcases ha with (⟨hp, hhp, rfl⟩ | ⟨gp, hgp, rfl⟩) | ha0
  · exact hzA ⟨hp, hhp⟩
  · exact rootedAdjoint_mem_of_isAmbient h_root h_sub
      (Hereditary.has_option hg (IsOption.of_mem_moves hgp))
  · by_cases hz : IsEnd (-p) g ∧ IsEnd (-p) h
    · simpa [hz, ha0] using h_root
    · simp [hz] at ha0

private theorem downlinkWitness_mem (h_root : A r) (h_sub : A ≤ IsAmbient)
    {g h : G} {x : moves .left g → G} {y : moves .right h → G}
    [Small (downlinkLeftSet r g h y)] [Small (downlinkRightSet r g h x)]
    (hg : IsAmbient g)
    (hh : IsAmbient h)
    (hxA : ∀ gl, A (x gl)) (hyA : ∀ hr, A (y hr)) :
    A (downlinkWitness r g h x y) := by
  let L : Set G := downlinkLeftSet r g h y
  let R : Set G := downlinkRightSet r g h x
  change A !{L | R}
  apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
  · exact downlinkOptions_mem h_root h_sub (p := .left) hg hyA
  · exact downlinkOptions_mem h_root h_sub (p := .right) hh hxA
  · exact downlinkOptions_nonempty r .left g h y
  · exact downlinkOptions_nonempty r .right h g x
  · exact Ambient.isAmbient_downlinkWitness (h_sub r h_root)
      hg hh
      (fun gl => h_sub _ (hxA gl))
      (fun hr => h_sub _ (hyA hr))

/--
If every Left option of `g` is separated from `h`, and every Right option of
`h` from `g`, then `g` is downlinked to `h`.
-/
theorem Downlinked.of_separating (h_root : A r) (h_isRoot : IsRoot IsAmbient r)
    (h_sub : A ≤ IsAmbient)
    {g h : G} (hg : IsAmbient g) (hh : IsAmbient h)
    (h_left_sep : ∀ gl : moves .left g, LeftSeparating A (gl : G) h)
    (h_right_sep : ∀ hr : moves .right h, RightSeparating A g (hr : G)) :
    Downlinked A g h := by
  classical
  choose x hxA hxLose hxWin using h_left_sep
  choose y hyA hyWin hyLose using h_right_sep
  haveI : Small.{u} (downlinkZero r .left g h) := by
    by_cases hz : IsEnd .right g ∧ IsEnd .right h
    · simpa [downlinkZero, hz] using (inferInstance : Small.{u} ({r} : Set G))
    · simpa [downlinkZero, hz] using (inferInstance : Small.{u} (∅ : Set G))
  haveI : Small.{u} (downlinkZero r .right h g) := by
    by_cases hz : IsEnd .left h ∧ IsEnd .left g
    · simpa [downlinkZero, hz] using (inferInstance : Small.{u} ({r} : Set G))
    · simpa [downlinkZero, hz] using (inferInstance : Small.{u} (∅ : Set G))
  haveI : Small.{u} (downlinkLeftSet r g h y) := inferInstance
  haveI : Small.{u} (downlinkRightSet r g h x) := inferInstance
  exact downlinked_of_downlinkWitness_mem h_isRoot hg hh
    (downlinkWitness_mem h_root h_sub hg hh hxA hyA) hxLose hxWin hyWin hyLose

/--
If `g ≱ h` modulo `A`, then `g` and `h` are both Left- and Right-separating.
-/
theorem Separating.pair_of_not_misereGE
    (h_root : A r) (h_isRoot : IsRoot IsAmbient r) (h_sub : A ≤ IsAmbient)
    {g h : G} (hg : IsAmbient g) (hh : IsAmbient h) (h_not_ge : ¬(g ≥m A h)) :
    LeftSeparating A g h ∧ RightSeparating A g h := by
  cases not_misereGE_iff_separating.mp h_not_ge with
  | inl h_left =>
      refine ⟨h_left, ?_⟩
      refine rightSeparating_of_leftSeparating_of_rightSeparatorCandidate_mem h_isRoot hh ?_ h_left
      intro x hx
      exact rightSeparatorCandidate_mem h_root h_sub hh hx
  | inr h_right =>
      refine ⟨?_, h_right⟩
      refine leftSeparating_of_rightSeparating_of_leftSeparatorCandidate_mem h_isRoot hg ?_ h_right
      intro x hx
      exact leftSeparatorCandidate_mem h_root h_sub hg hx

/--
A dicotically closed `A` lying in the ambient space and containing a *root* `r`
(see `IsRoot`) is a `ComparisonSet` (no further closure properties required!).
Taking `r = 0` recovers the usual case where `A` contains `0`.
-/
def ComparisonSet.of_dicotic (h_root : A r) (h_isRoot : IsRoot IsAmbient r)
    (h_sub : A ≤ IsAmbient) :
    ComparisonSet IsAmbient A where
  separating_pair_of_not_misereGE hg hh h_not_ge :=
    Separating.pair_of_not_misereGE h_root h_isRoot h_sub hg hh h_not_ge
  downlinked_of_separating hg hh h_left_sep h_right_sep :=
    Downlinked.of_separating h_root h_isRoot h_sub hg hh h_left_sep h_right_sep

/--
A nonempty, hereditary, dicotically closed `A` lying in the ambient space is a
`ComparisonSet`. The zero-like form it must contain (`exists_isZeroLike`)
serves as the required root.
-/
def ComparisonSet.of_dicotic_of_nonempty [Hereditary A] (h_ne : ∃ g, A g)
    (h_sub : A ≤ IsAmbient) :
    ComparisonSet IsAmbient A :=
  let ⟨_, hr, hr_zero⟩ := exists_isZeroLike h_ne
  .of_dicotic hr (isRoot_of_isZeroLike IsAmbient hr_zero) h_sub

end

namespace ComparisonSet

section

variable [Ambient IsAmbient] [Universe IsAmbient A]

instance instComparisonSetUniverse : ComparisonSet IsAmbient A :=
  .of_dicotic_of_nonempty ⟨0, Universe.zero_mem IsAmbient⟩
    (fun _ ha => Universe.isAmbient_of_mem ha)

end

variable [ComparisonSet IsAmbient A]

-- TODO: Remove and use class member?
/--
If $G\ngeq_\mathcal{A}H$, then $G$ and $H$ must be both `LeftSeparating` and
`RightSeparating`. This generalises a result of [Siegel (Lemma 5.8 on p.
214)][siegel:GeneralDeadendingUniverse:2025], which proved it only for short
augmented forms and short universes.
-/
lemma leftSeparating_rightSeparating_of_not_misereGE
    {g h : G}
    (hg : IsAmbient g) (hh : IsAmbient h) (h_not_ge : ¬(g ≥m A h)) :
    LeftSeparating A g h ∧ RightSeparating A g h := by
  exact separating_pair_of_not_misereGE hg hh h_not_ge

/--
If $\nexists G^L$ such that $G^L\ge_\mathcal{A}H$, and $\nexists H^R$ such that
$G\ge_\mathcal{A}H^R$, then $G$ must be downlinked to $H$.

This is a transfinite generalisation of one half of a result of [Siegel (Lemma
5.10 on p. 214)][siegel:GeneralDeadendingUniverse:2025].
-/
lemma downlinked_of_not_exists_moves_misereGE
    {g h : G}
    (hg : IsAmbient g) (hh : IsAmbient h)
    (h_left : ¬∃ gl ∈ moves .left g, gl ≥m A h)
    (h_right : ¬∃ hr ∈ moves .right h, g ≥m A hr) :
    Downlinked A g h := by
  have h_left_sep : ∀ gl : moves .left g, LeftSeparating A (gl : G) h := by
    intro gl
    have h_not_ge : ¬((gl : G) ≥m A h) := fun hge => h_left ⟨gl, gl.prop, hge⟩
    exact (leftSeparating_rightSeparating_of_not_misereGE
      (Hereditary.has_option hg (IsOption.of_mem_moves gl.prop)) hh h_not_ge).left
  have h_right_sep : ∀ hr : moves .right h, RightSeparating A g (hr : G) := by
    intro hr
    have h_not_ge : ¬(g ≥m A (hr : G)) := fun hge => h_right ⟨hr, hr.prop, hge⟩
    exact (leftSeparating_rightSeparating_of_not_misereGE
      hg (Hereditary.has_option hh (IsOption.of_mem_moves hr.prop)) h_not_ge).right
  exact downlinked_of_separating hg hh h_left_sep h_right_sep

private lemma not_misereGE_of_right_left_outcomes
    {g h t : G} (hge : g ≥m A h) (ht : A t) (p : Player)
    (hgt : MiserePlayerOutcome (g + t) p = .right)
    (hht : MiserePlayerOutcome (h + t) p = .left) : False := by
  have h_cmp := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (hge t ht) p
  rw [hgt, hht] at h_cmp
  exact Player.left_le_right h_cmp

private lemma not_downlinked_left_option_of_misereGE
    {g h hl : G} (hge : g ≥m A h) (hhl : hl ∈ moves .left h) :
    ¬Downlinked A g hl := by
  rintro ⟨t, ht, hgt, hhlt⟩
  have hgt_out : MiserePlayerOutcome (g + t) .left = .right := by
    unfold MiserePlayerOutcome
    simp [hgt]
  have hhlt_out : MiserePlayerOutcome (hl + t) .right = .left := by
    unfold MiserePlayerOutcome
    simp [hhlt]
  have hht : MiserePlayerOutcome (h + t) .left = .left :=
    miserePlayerOutcome_of_leftMoves (add_right_mem_moves_add hhl t) hhlt_out
  exact not_misereGE_of_right_left_outcomes hge ht .left hgt_out hht

private lemma not_downlinked_right_option_of_misereGE
    {g h gr : G} (hge : g ≥m A h) (hgr : gr ∈ moves .right g) :
    ¬Downlinked A gr h := by
  rintro ⟨t, ht, hgrt, hht⟩
  have hgrt_out : MiserePlayerOutcome (gr + t) .left = .right := by
    unfold MiserePlayerOutcome
    simp [hgrt]
  have hgt : MiserePlayerOutcome (g + t) .right = .right :=
    miserePlayerOutcome_of_rightMoves (add_right_mem_moves_add hgr t) hgrt_out
  have hht_out : MiserePlayerOutcome (h + t) .right = .left := by
    unfold MiserePlayerOutcome
    simp [hht]
  exact not_misereGE_of_right_left_outcomes hge ht .right hgt hht_out

private lemma maintenance_of_misereGE
    {g h : G} (p : Player)
    (hg : IsAmbient g) (hh : IsAmbient h) (hge : g ≥m A h) :
    Maintenance A g h p := by
  cases p
  · intro hl hhl
    by_contra h_not
    have h_downlinked : Downlinked A g hl := by
      apply downlinked_of_not_exists_moves_misereGE hg
        (Hereditary.has_option hh (IsOption.of_mem_moves hhl))
      · intro h_exists
        exact h_not (Or.inl h_exists)
      · intro h_exists
        exact h_not (Or.inr h_exists)
    exact not_downlinked_left_option_of_misereGE hge hhl h_downlinked
  · intro gr hgr
    by_contra h_not
    have h_downlinked : Downlinked A gr h := by
      apply downlinked_of_not_exists_moves_misereGE
        (Hereditary.has_option hg (IsOption.of_mem_moves hgr)) hh
      · intro h_exists
        exact h_not (Or.inr h_exists)
      · intro h_exists
        exact h_not (Or.inl h_exists)
    exact not_downlinked_right_option_of_misereGE hge hgr h_downlinked

/--
If $G\ge_\mathcal{A}H$, then $G$ and $H$ must satisfy both the
`Form.Maintenance` and the `Form.Proviso`.
-/
theorem maintenance_proviso_of_misereGE
    {g h : G}
    (hg : IsAmbient g) (hh : IsAmbient h) :
    g ≥m A h →
      Maintenance A g h .right ∧ Maintenance A g h .left ∧
      Proviso A g h .right ∧ Proviso A h g .left := by
  intro hge
  exact ⟨maintenance_of_misereGE .right hg hh hge,
    maintenance_of_misereGE .left hg hh hge,
    proviso_right_of_misereGE hge,
    proviso_left_of_misereGE hge⟩

/--
If $\mathcal{A}$ is hereditary, contains `0`, and is dicotically closed, then
$G\ge_\mathcal{A}H$ if and only if $G$ and $H$ satisfy both the
`Form.Maintenance` and the `Form.Proviso`.
-/
theorem misereGE_iff_maintenance_proviso [Hereditary A] : Promain IsAmbient A := by
  intro g h h_g h_h
  constructor
  · intro h_ge
    exact maintenance_proviso_of_misereGE (IsAmbient := IsAmbient) h_g h_h h_ge
  · intro ⟨h_mghr, h_mghl, h_pghr, h_pghl⟩
    exact Hereditary.misereGE_of_maintenance_proviso A h_mghr h_mghl h_pghr h_pghl

end ComparisonSet

namespace Maintenance

theorem of_subset {A B : G → Prop} (h_subset : ∀ g, B g → A g) {g h : G} {p : Player}
    (h_maintenance : Maintenance A g h p) : Maintenance B g h p := by
  have h_ge {x y : G} (hxy : x ≥m A y) : x ≥m B y := misereGE_of_subset A h_subset x y hxy
  cases p <;>
    exact fun y hy => (h_maintenance y hy).imp
      (Exists.imp fun _ => And.imp_right h_ge)
      (Exists.imp fun _ => And.imp_right h_ge)

end Maintenance

end Form
