/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import CombinatorialGames.Form.Misere.Adjoint
public import CombinatorialGames.Misere.Hereditary
public import CombinatorialGames.Misere.Universe

/-!
# Separation and downlinking

This file defines downlinked and separated pairs of forms, and develops the
machinery necessary to prove that $G\ge_\mathcal{U}H$ implies that both
`Form.Maintenance` and `Form.Proviso` are satisfied.

Here, $G$ and $H$ will always refer to arbitrary forms (possibly augmented,
possibly not), $\mathcal{A}$ to an arbitrary set of forms, and $\mathcal{U}$ to
a universe (which may or may not be `Short`).

## References

* [A. N. Siegel, *On the general dead-ending universe of partizan games*
(Section 5 on pp. 207–222)][siegel:GeneralDeadendingUniverse:2025]
-/

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Form.Misere.Adjoint
open Form.Misere.Outcome

public section

namespace Form

/--
We say $G$ is _downlinked_ to $H$ (with respect to $\mathcal{A}$) if there
exists some $T\in\mathcal{A}$ with $\operatorname{o_L}(G+T)=\mathscr{R}$ and
$\operatorname{o_R}(H+T)=\mathscr{L}$.

This generalises the definition given by [Siegel (Definition 5.9 on p.
214)][siegel:GeneralDeadendingUniverse:2025], where all forms were short, and
the sets were short universes.
-/
@[expose] def Downlinked (A : G → Prop) (g h : G) : Prop :=
  ∃ t, A t ∧ ¬WinsGoingFirst .left (g + t) ∧
    ¬WinsGoingFirst .right (h + t)


/--
If there exists some $X\in\mathcal{A}$ whereby
$\operatorname{o_L}(G+X)=\mathscr{R}$ and
$\operatorname{o_L}(H+X)=\mathscr{L}$, then we say that $G$ and $H$ are _Left
separated_ (with respect to $\mathcal{A}$). (See `LeftSeparating` and
`RightSeparating`.)
-/
@[expose] def Separating (A : G → Prop) (p : Player) (g h : G) : Prop :=
  match p with
  | .left => ∃ x, A x ∧ ¬WinsGoingFirst .left (g + x) ∧
      WinsGoingFirst .left (h + x)
  | .right => ∃ x, A x ∧ WinsGoingFirst .right (g + x) ∧
      ¬WinsGoingFirst .right (h + x)

/--
There exists some $X\in\mathcal{A}$ whereby
$\operatorname{o_L}(G+X)=\mathscr{R}$ and
$\operatorname{o_L}(H+X)=\mathscr{L}$. (See `Separating`.)
-/
abbrev LeftSeparating (A : G → Prop) (g h : G) : Prop :=
  Separating A .left g h

/--
There exists some $X\in\mathcal{A}$ whereby
$\operatorname{o_R}(G+X)=\mathscr{R}$ and
$\operatorname{o_R}(H+X)=\mathscr{L}$. (See `Separating`.)
-/
abbrev RightSeparating (A : G → Prop) (g h : G) : Prop :=
  Separating A .right g h

/--
If $G\ngeq_\mathcal{A}H$, then $G$ and $H$ must be at least one of
`LeftSeparating` and `RightSeparating`. When $\mathcal{A}$ is a universe,
`leftSeparating_rightSeparating_of_not_misereGE` proves that in fact $G$ and
$H$ must always be both.
-/
lemma leftSeparating_or_rightSeparating_of_not_misereGE {A : G → Prop}
    {g h : G} (h_not_ge : ¬(g ≥m A h)) :
    LeftSeparating A g h ∨ RightSeparating A g h := by
      /-
        At a lower level, the proof could be understood as follows. We know
        that ¬(g ≥ h), and so there exists some x with ¬(o(g+x) ≥ o(h+x)).
        Given our four outcomes classes, the only possibilites for
        (o(g+x),o(h+x)) are:

        - (N,L)
        - (P,L)
        - (R,L)
        - (P,N)
        - (R,N)
        - (N,P)
        - (R,P)

        In each of these cases, it is trivial to check the required condition.
      -/
  rw [MisereGE] at h_not_ge
  simp only [not_forall] at h_not_ge
  obtain ⟨x, hx, h_not_outcome_ge⟩ := h_not_ge
  have h_not_player_ge :
      ¬∀ p, MiserePlayerOutcome (g + x) p ≥ MiserePlayerOutcome (h + x) p := by
    intro h_player_ge
    exact h_not_outcome_ge (misereOutcome_ge_iff_miserePlayerOutcome_ge.mpr h_player_ge)
  simp only [Player.forall, not_and_or] at h_not_player_ge
  cases h_not_player_ge with
  | inl h_left =>
      left
      cases hg : MiserePlayerOutcome (g + x) .left
      <;> cases hh : MiserePlayerOutcome (h + x) .left
      <;> simp [hg, hh] at h_left
      refine ⟨x, hx, ?_, ?_⟩
      · intro h_win
        have h_out := miserePlayerOutcome_eq_iff_winsGoingFirst.mpr h_win
        rw [hg] at h_out
        cases h_out
      · exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp hh
  | inr h_right =>
      right
      cases hg : MiserePlayerOutcome (g + x) .right
      <;> cases hh : MiserePlayerOutcome (h + x) .right
      <;> simp [hg, hh] at h_right
      refine ⟨x, hx, ?_, ?_⟩
      · exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp hg
      · intro h_win
        have h_out := miserePlayerOutcome_eq_iff_winsGoingFirst.mpr h_win
        rw [hh] at h_out
        cases h_out

namespace Separation

/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
Given $H$, this constructs the set of games $\{0,(H^\mathcal{R})^\circ\}$,
which will act as Left's set of options in the construction of
`rightSeparatorCandidate`.
-/
abbrev rightSeparatorLeftSet (h : G) : Set G :=
  {0} ∪ Set.range (fun hr : moves .right h => (hr : G)°)

/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
Given forms $H$ and $X$, this constructs the form
$\form<0,(H^\mathcal{R})^\circ>[X]$, which is used by
`leftSeparating_rightSeparating_of_not_misereGE` to show that $G$ and $H$ must
be both `LeftSeparating` and `RightSeparating` whenever $G\ngeq_\mathcal{U}H$.
-/
noncomputable abbrev rightSeparatorCandidate (h x : G) : G :=
  !{rightSeparatorLeftSet h | {x}}

/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
If $G$ and $H$ are `LeftSeparating`, and
$\form<0,(H^\mathcal{R})^\circ>[X]\in\mathcal{A}$ for every $X\in\mathcal{A}$,
then $G$ and $H$ are `RightSeparating`.
-/
lemma rightSeparating_of_leftSeparating_of_rightSeparatorCandidate_mem
    {A : G → Prop} {g h : G}
    (h_candidate : ∀ {x : G}, A x → A (rightSeparatorCandidate h x))
    (h_left_sep : LeftSeparating A g h) :
    RightSeparating A g h := by
  obtain ⟨x, hx, hgx, hhx⟩ := h_left_sep
  let y := rightSeparatorCandidate h x
  have hy : A y := h_candidate hx
  refine ⟨y, hy, ?_, ?_⟩
  · apply winsGoingFirst_of_moves
    refine ⟨g + x, ?_, ?_⟩
    · apply add_left_mem_moves_add
      change x ∈ moves .right (rightSeparatorCandidate h x)
      unfold rightSeparatorCandidate
      rw [rightMoves_ofSets (s := rightSeparatorLeftSet h) (t := {x})]
      simp only [Set.mem_singleton_iff]
    · exact hgx
  · rw [not_winsGoingFirst_iff]
    constructor
    · intro h_end
      have hy_end : IsEndLike .right y := (IsEndLike.add_iff.mp h_end).right
      rw [ofSets_isEndLike_iff, isEnd_def, rightMoves_ofSets] at hy_end
      exact Set.singleton_ne_empty x hy_end
    · intro k hk
      rw [moves_add] at hk
      cases hk with
      | inl h_h_move =>
          obtain ⟨hr, hhr, rfl⟩ := h_h_move
          apply winsGoingFirst_of_moves
          refine ⟨hr + hr°, ?_, ?_⟩
          · apply add_left_mem_moves_add
            change hr° ∈ moves .left (rightSeparatorCandidate h x)
            unfold rightSeparatorCandidate
            rw [leftMoves_ofSets (s := rightSeparatorLeftSet h) (t := {x})]
            simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
            right
            exact ⟨⟨hr, hhr⟩, rfl⟩
          · exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P hr)
      | inr h_y_move =>
          obtain ⟨yr, hyr, rfl⟩ := h_y_move
          change yr ∈ moves .right (rightSeparatorCandidate h x) at hyr
          unfold rightSeparatorCandidate at hyr
          rw [rightMoves_ofSets (s := rightSeparatorLeftSet h) (t := {x})] at hyr
          simp only [Set.mem_singleton_iff] at hyr
          rw [hyr]
          exact hhx

open Classical

public abbrev downlinkZero (p : Player) (g h : G) : Set G :=
  if IsEnd (-p) g ∧ IsEnd (-p) h then {0} else ∅

public abbrev downlinkOptions (p : Player) (g h : G) (z : moves (-p) h → G) : Set G :=
  Set.range z ∪ Set.range (fun gp : moves (-p) g => (gp : G)°) ∪ downlinkZero p g h

abbrev downlinkLeftSet (g h : G) (y : moves .right h → G) : Set G :=
  downlinkOptions .left g h y

abbrev downlinkRightSet (g h : G) (x : moves .left g → G) : Set G :=
  downlinkOptions .right h g x

lemma downlinkOptions_nonempty
    (p : Player) (g h : G) (z : moves (-p) h → G) :
    (downlinkOptions p g h z).Nonempty := by
  by_cases hz : IsEnd (-p) g ∧ IsEnd (-p) h
  · exact ⟨0, by simp [downlinkOptions, downlinkZero, hz]⟩
  · rw [not_and_or] at hz
    cases hz with
    | inl hg =>
        obtain ⟨gp, hgp⟩ := not_isEnd_exists_move hg
        exact ⟨gp°, by
          simp only [downlinkOptions, Set.mem_union, Set.mem_range]
          exact Or.inl (Or.inr ⟨⟨gp, hgp⟩, rfl⟩)⟩
    | inr hh =>
        obtain ⟨hp, hhp⟩ := not_isEnd_exists_move hh
        exact ⟨z ⟨hp, hhp⟩, by
          simp only [downlinkOptions, Set.mem_union, Set.mem_range]
          exact Or.inl (Or.inl ⟨⟨hp, hhp⟩, rfl⟩)⟩

/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
This constructs the following game form, which is similar to a construction by
[Siegel (Proof of Lemma 5.10 on p. 215)][siegel:GeneralDeadendingUniverse:2025]
for short forms:
$$
T=
\begin{cases}
*
& \text{if neither }G\text{ nor }H\text{ has any ordinary options},\\
\form<0>[X_i,(H^\mathcal{L})^\circ]
& \text{if }G,H\text{ are both Right ends but not both Left ends},\\
\form<Y_j,(G^\mathcal{R})^\circ>[0]
& \text{if }G,H\text{ are both Left ends but not both Right ends},\\
\form<Y_j,(G^\mathcal{R})^\circ>[X_i,(H^\mathcal{L})^\circ]
& \text{otherwise}.
\end{cases}
$$

(Note that the $X_i$ and $Y_j$ are chosen as a function of the Left and Right
options of $G$ and $H$ respectively.)
-/
noncomputable abbrev downlinkWitness
    (g h : G) (x : moves .left g → G) (y : moves .right h → G)
    [Small (downlinkLeftSet g h y)] [Small (downlinkRightSet g h x)] : G :=
  !{downlinkLeftSet g h y | downlinkRightSet g h x}

private lemma downlinked_of_downlinkWitness_mem
    {A : G → Prop} {g h : G}
    {x : moves .left g → G} {y : moves .right h → G}
    [Small (downlinkLeftSet g h y)] [Small (downlinkRightSet g h x)]
    (htA : A (downlinkWitness g h x y))
    (hxLose : ∀ gl : moves .left g, ¬WinsGoingFirst .left ((gl : G) + x gl))
    (hxWin : ∀ gl : moves .left g, WinsGoingFirst .left (h + x gl))
    (hyWin : ∀ hr : moves .right h, WinsGoingFirst .right (g + y hr))
    (hyLose : ∀ hr : moves .right h, ¬WinsGoingFirst .right ((hr : G) + y hr)) :
    Downlinked A g h := by
  let L := downlinkLeftSet g h y
  let R := downlinkRightSet g h x
  let t : G := !{L | R}
  have hLnonempty : L.Nonempty := downlinkOptions_nonempty .left g h y
  have hRnonempty : R.Nonempty := downlinkOptions_nonempty .right h g x
  change A t at htA
  refine ⟨t, htA, ?_, ?_⟩
  all_goals
    rw [not_winsGoingFirst_iff]
    refine ⟨?_, ?_⟩
  · intro hEnd
    apply hLnonempty.ne_empty
    simpa [t, L, ofSets_isEndLike_iff, isEnd_def] using
      (IsEndLike.add_iff.mp hEnd).right
  · rw [moves_add]
    rintro k (⟨gl, hgl, rfl⟩ | ⟨tl, htl, rfl⟩)
    · exact winsGoingFirst_of_moves ⟨gl + x ⟨gl, hgl⟩,
        add_left_mem_moves_add (by simp [t, R, downlinkRightSet, downlinkOptions]) gl,
        hxLose ⟨gl, hgl⟩⟩
    · simp [t, L, downlinkLeftSet, downlinkOptions, downlinkZero] at htl
      rcases htl with (⟨hr, hhr, rfl⟩ | ⟨gr, hgr, rfl⟩) | htl_zero
      · exact hyWin ⟨hr, hhr⟩
      · exact winsGoingFirst_of_moves ⟨gr + gr°,
          add_right_mem_moves_add hgr (gr°),
          not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P gr)⟩
      · by_cases hz : IsEnd .right g ∧ IsEnd .right h
        all_goals simp [hz] at htl_zero
        simpa [htl_zero] using
          (winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨hz.left, isEnd_zero⟩) :
            WinsGoingFirst .right (g + 0))
  · intro hEnd
    apply hRnonempty.ne_empty
    simpa [t, R, ofSets_isEndLike_iff, isEnd_def] using
      (IsEndLike.add_iff.mp hEnd).right
  · rw [moves_add]
    rintro k (⟨hr, hhr, rfl⟩ | ⟨tr, htr, rfl⟩)
    · exact winsGoingFirst_of_moves ⟨hr + y ⟨hr, hhr⟩,
        add_left_mem_moves_add (by simp [t, L, downlinkLeftSet, downlinkOptions]) hr,
        hyLose ⟨hr, hhr⟩⟩
    · simp [t, R, downlinkRightSet, downlinkOptions, downlinkZero] at htr
      rcases htr with (⟨gl, hgl, rfl⟩ | ⟨hl, hhl, rfl⟩) | htr_zero
      · exact hxWin ⟨gl, hgl⟩
      · exact winsGoingFirst_of_moves ⟨hl + hl°,
          add_right_mem_moves_add hhl (hl°),
          not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P hl)⟩
      · by_cases hz : IsEnd .left h ∧ IsEnd .left g
        all_goals simp [hz] at htr_zero
        simpa [htr_zero] using
          (winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨hz.left, isEnd_zero⟩) :
            WinsGoingFirst .left (h + 0))

/--
If $G$ and $H$ are `RightSeparating`, then $\overline{H}$ and $\overline{G}$
must be `LeftSeparating`.
-/
lemma leftSeparating_neg_of_rightSeparating {A : G → Prop} [ClosedUnderNeg A]
    {g h : G} (h_right_sep : RightSeparating A g h) :
    LeftSeparating A (-h) (-g) := by
  obtain ⟨y, hy, hgy, hhy⟩ := h_right_sep
  refine ⟨-y, ClosedUnderNeg.neg_of hy, ?_, ?_⟩
  · intro h_win
    have h_win' : WinsGoingFirst .right (h + y) := by
      apply (winsGoingFirst_neg_iff (h + y) .left).mp
      simpa [neg_add_rev, add_comm] using h_win
    exact hhy h_win'
  · have h_win : WinsGoingFirst .left (-(g + y)) :=
      (winsGoingFirst_neg_iff (g + y) .left).mpr hgy
    simpa [neg_add_rev, add_comm] using h_win

/--
If $\overline{H}$ and $\overline{G}$ are `RightSeparating`, then $G$ and $H$
must be `LeftSeparating`.
-/
lemma leftSeparating_of_rightSeparating_neg {A : G → Prop} [ClosedUnderNeg A]
    {g h : G} (h_right_sep : RightSeparating A (-h) (-g)) :
    LeftSeparating A g h := by
  simpa using (leftSeparating_neg_of_rightSeparating h_right_sep)

/--
This is an interface used to show that $G\ge_\mathcal{U}H$ implies
`Form.Maintenance` and `Form.Proviso` (see `maintenance_proviso_of_misereGE`).

The `IsAmbient` predicate dictates what game forms exist in the ambient space
for comparison. For example, in a `ShortUniverse`, `IsAmbient` is
`Form.IsShort`. We require the set of ambient forms to be `Form.Hereditary`.
The final two fields assert that our separating and downlink constructions are
always elements of `A`.
-/
class ComparisonSet (A : G → Prop) where
  IsAmbient : G → Prop
  hereditary : Hereditary IsAmbient
  separating_pair_of_not_misereGE {g h : G} :
    IsAmbient g → IsAmbient h → ¬(g ≥m A h) →
      LeftSeparating A g h ∧ RightSeparating A g h
  downlinkWitness_mem {g h : G} {x : moves .left g → G} {y : moves .right h → G}
    [Small (downlinkLeftSet g h y)] [Small (downlinkRightSet g h x)] :
    IsAmbient g → IsAmbient h → (∀ gl, A (x gl)) → (∀ hr, A (y hr)) →
      A (downlinkWitness g h x y)

attribute [instance] ComparisonSet.hereditary

namespace ComparisonSet

/--
This adapter adds data to the structure of the ambient space of a `Universe` so
that the required witnesses for `ComparisonSet` can be constructed.
-/
class UniverseAdapter (IsAmbient : outParam (G → Prop)) (A : G → Prop) extends
    Universe IsAmbient A where
  isAmbient_hereditary : Hereditary IsAmbient
  isAmbient_closed_neg : ClosedUnderNeg IsAmbient
  isAmbient_adjoint {g : G} : IsAmbient g → IsAmbient (g°)
  isAmbient_rightSeparatorCandidate {h x : G} :
    IsAmbient h → IsAmbient x → IsAmbient (rightSeparatorCandidate h x)
  isAmbient_downlinkWitness {g h : G} {x : moves .left g → G} {y : moves .right h → G}
    [Small (downlinkLeftSet g h y)] [Small (downlinkRightSet g h x)] :
    IsAmbient g → IsAmbient h → (∀ gl, IsAmbient (x gl)) → (∀ hr, IsAmbient (y hr)) →
      IsAmbient (downlinkWitness g h x y)

attribute [instance] UniverseAdapter.isAmbient_hereditary
attribute [instance] UniverseAdapter.isAmbient_closed_neg

namespace UniverseAdapter

variable {IsAmbient A : G → Prop} [UniverseAdapter IsAmbient A]

private theorem universe_zero_mem (IsAmbient : G → Prop) {A : G → Prop}
    [UniverseAdapter IsAmbient A] : A 0 :=
  Universe.zero_mem IsAmbient (A := A)

/--
The adjoint of a form in the ambient space is always in the universe (adapter).
-/
theorem adjoint_mem {g : G} (hg : IsAmbient g) : A (g°) := by
  have hzero : ∀ a ∈ ({0} : Set G), A a := by
    intro a ha
    rw [Set.mem_singleton_iff.mp ha]
    exact universe_zero_mem IsAmbient
  have hzero_nonempty : ({0} : Set G).Nonempty := Set.singleton_nonempty 0
  have hAdjAmbient := UniverseAdapter.isAmbient_adjoint
    (IsAmbient := IsAmbient) (A := A) hg
  have hAdjRange : ∀ p, ∀ a ∈ Set.range (fun gp : moves p g => (gp : G)°), A a := by
    intro p a ha
    simp only [Set.mem_range, Subtype.exists, exists_prop] at ha
    obtain ⟨gp, hgp, rfl⟩ := ha
    exact adjoint_mem (Hereditary.has_option hg (IsOption.of_mem_moves hgp))
  have hAdjRange_nonempty :
      ∀ {p}, ¬IsEnd p g → (Set.range fun gp : moves p g => (gp : G)°).Nonempty := by
    intro p hp
    obtain ⟨gp, hgp⟩ := not_isEnd_exists_move hp
    exact ⟨gp°, ⟨⟨gp, hgp⟩, rfl⟩⟩
  unfold adjoint
  by_cases hleft : IsEnd .left g
  · by_cases hright : IsEnd .right g
    · simp [hleft, hright]
      apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
      · exact hzero
      · exact hzero
      · exact hzero_nonempty
      · exact hzero_nonempty
      · unfold adjoint at hAdjAmbient
        simpa [hleft, hright] using hAdjAmbient
    · simp [hleft, hright]
      apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
      · exact hAdjRange .right
      · exact hzero
      · exact hAdjRange_nonempty hright
      · exact hzero_nonempty
      · unfold adjoint at hAdjAmbient
        simpa [hleft, hright] using hAdjAmbient
  · by_cases hright : IsEnd .right g
    · simp [hleft, hright]
      apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
      · exact hzero
      · exact hAdjRange .left
      · exact hzero_nonempty
      · exact hAdjRange_nonempty hleft
      · unfold adjoint at hAdjAmbient
        simpa [hleft, hright] using hAdjAmbient
    · simp [hleft, hright]
      apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
      · exact hAdjRange .right
      · exact hAdjRange .left
      · exact hAdjRange_nonempty hright
      · exact hAdjRange_nonempty hleft
      · unfold adjoint at hAdjAmbient
        simpa [hleft, hright] using hAdjAmbient
termination_by g
decreasing_by all_goals form_wf

private theorem rightSeparatorLeftSet_mem {h : G} (hh : IsAmbient h) :
    ∀ b ∈ rightSeparatorLeftSet h, A b := by
  intro b hb
  simp only [rightSeparatorLeftSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hb
  rcases hb with rfl | ⟨hr, rfl⟩
  · exact universe_zero_mem IsAmbient
  · exact adjoint_mem (Hereditary.has_option hh (IsOption.of_mem_moves hr.prop))

theorem rightSeparatorCandidate_mem_of_comparison {h x : G} (hh : IsAmbient h) (hx : A x) :
    A (rightSeparatorCandidate h x) := by
  unfold rightSeparatorCandidate
  apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
  · exact rightSeparatorLeftSet_mem hh
  · intro c hc
    rwa [Set.mem_singleton_iff.mp hc]
  · exact ⟨0, Or.inl rfl⟩
  · exact Set.singleton_nonempty x
  · exact UniverseAdapter.isAmbient_rightSeparatorCandidate
      (IsAmbient := IsAmbient) (A := A) hh (Universe.isAmbient_of_mem hx)

private theorem downlinkOptions_mem {p : Player} {g h : G} {z : moves (-p) h → G}
    (hg : IsAmbient g) (hzA : ∀ hp, A (z hp)) :
    ∀ a ∈ downlinkOptions p g h z, A a := by
  intro a ha
  simp [downlinkOptions, downlinkZero] at ha
  rcases ha with (⟨hp, hhp, rfl⟩ | ⟨gp, hgp, rfl⟩) | ha0
  · exact hzA ⟨hp, hhp⟩
  · exact adjoint_mem (Hereditary.has_option hg (IsOption.of_mem_moves hgp))
  · by_cases hz : IsEnd (-p) g ∧ IsEnd (-p) h
    · simpa [hz, ha0] using (universe_zero_mem IsAmbient (A := A))
    · simp [hz] at ha0

theorem downlinkWitness_mem_of_comparison
    {g h : G} {x : moves .left g → G} {y : moves .right h → G}
    [Small (downlinkLeftSet g h y)] [Small (downlinkRightSet g h x)]
    (hg : IsAmbient g)
    (hh : IsAmbient h)
    (hxA : ∀ gl, A (x gl)) (hyA : ∀ hr, A (y hr)) :
    A (downlinkWitness g h x y) := by
  let L : Set G := downlinkLeftSet g h y
  let R : Set G := downlinkRightSet g h x
  change A !{L | R}
  apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
  · exact downlinkOptions_mem (p := .left) hg hyA
  · exact downlinkOptions_mem (p := .right) hh hxA
  · exact downlinkOptions_nonempty .left g h y
  · exact downlinkOptions_nonempty .right h g x
  · exact UniverseAdapter.isAmbient_downlinkWitness
      (IsAmbient := IsAmbient) (A := A) hg hh
      (fun gl => Universe.isAmbient_of_mem (hxA gl))
      (fun hr => Universe.isAmbient_of_mem (hyA hr))

instance : ComparisonSet A where
  IsAmbient := IsAmbient
  hereditary := inferInstance
  separating_pair_of_not_misereGE {g} {h} hg hh h_not_ge := by
    cases leftSeparating_or_rightSeparating_of_not_misereGE h_not_ge with
    | inl h_left =>
        refine ⟨h_left, ?_⟩
        refine rightSeparating_of_leftSeparating_of_rightSeparatorCandidate_mem ?_ h_left
        intro x hx
        exact rightSeparatorCandidate_mem_of_comparison hh hx
    | inr h_right =>
        refine ⟨?_, h_right⟩
        have h_not_ge_neg : ¬((-h) ≥m A (-g)) := by
          rwa [ClosedUnderNeg.neg_ge_neg_iff]
        have h_left_sep_neg : LeftSeparating A (-h) (-g) :=
          leftSeparating_neg_of_rightSeparating h_right
        have h_right_sep_neg : RightSeparating A (-h) (-g) := by
          refine rightSeparating_of_leftSeparating_of_rightSeparatorCandidate_mem ?_ h_left_sep_neg
          intro x hx
          exact rightSeparatorCandidate_mem_of_comparison (ClosedUnderNeg.neg_of hg) hx
        exact leftSeparating_of_rightSeparating_neg h_right_sep_neg
  downlinkWitness_mem := downlinkWitness_mem_of_comparison

end UniverseAdapter

end ComparisonSet

-- TODO: move this elsewhere
private theorem maintenance_neg
    {A : G → Prop} [ClosedUnderNeg A] {g h : G} {p : Player}
    (h_maintenance : Maintenance A (-h) (-g) (-p)) :
    Maintenance A g h p := by
  cases p
  · intro hl hhl
    rcases h_maintenance (-hl) (by simp [moves_neg, hhl]) with hopt | hreply
    · rcases hopt with ⟨ngl, hngl, hge⟩
      left
      refine ⟨-ngl, ?_, ?_⟩
      · simpa [moves_neg] using hngl
      · exact (ClosedUnderNeg.neg_ge_neg_iff (-ngl) hl).mp (by simpa using hge)
    · rcases hreply with ⟨nhlr, hnhlr, hge⟩
      right
      refine ⟨-nhlr, ?_, ?_⟩
      · simpa [moves_neg] using hnhlr
      · exact (ClosedUnderNeg.neg_ge_neg_iff g (-nhlr)).mp (by simpa using hge)
  · intro gr hgr
    rcases h_maintenance (-gr) (by simp [moves_neg, hgr]) with hopt | hreply
    · rcases hopt with ⟨nhr, hnhr, hge⟩
      left
      refine ⟨-nhr, ?_, ?_⟩
      · simpa [moves_neg] using hnhr
      · exact (ClosedUnderNeg.neg_ge_neg_iff gr (-nhr)).mp (by simpa using hge)
    · rcases hreply with ⟨ngrl, hngrl, hge⟩
      right
      refine ⟨-ngrl, ?_, ?_⟩
      · simpa [moves_neg] using hngrl
      · exact (ClosedUnderNeg.neg_ge_neg_iff (-ngrl) h).mp (by simpa using hge)

-- TODO: move this elsewhere
theorem maintenance_neg_iff
    {A : G → Prop} [ClosedUnderNeg A] {g h : G} (p : Player) :
    Maintenance A (-h) (-g) (-p) ↔ Maintenance A g h p := by
  constructor
  · exact maintenance_neg
  · intro hm
    have hm_neg : Maintenance A (- -g) (- -h) (- -p) := by simpa using hm
    simpa using maintenance_neg (g := -h) (h := -g) (p := -p) hm_neg

-- TODO: move this elsewhere
private theorem proviso_neg
    {A : G → Prop} [ClosedUnderNeg A] {g h : G} {p : Player}
    (h_proviso : Proviso A (-g) (-h) (-p)) :
    Proviso A g h p := by
  intro hg_end x hx hx_end
  have hwin_neg : WinsGoingFirst (-p) ((-h) + (-x)) :=
    h_proviso (by simpa [IsEndLike.neg_iff_neg] using hg_end)
      (-x) (ClosedUnderNeg.neg_of hx)
      (by simpa [IsEndLike.neg_iff_neg] using hx_end)
  rw [← winsGoingFirst_neg_iff, neg_add_rev, neg_neg, neg_neg, add_comm] at hwin_neg
  exact hwin_neg

-- TODO: move this elsewhere
theorem proviso_neg_iff
    {A : G → Prop} [ClosedUnderNeg A] {g h : G} (p : Player) :
    Proviso A (-g) (-h) (-p) ↔ Proviso A g h p := by
  constructor
  · exact proviso_neg
  · intro hp
    have hp_neg : Proviso A (- -g) (- -h) (- -p) := by simpa using hp
    simpa using proviso_neg (g := -g) (h := -h) (p := -p) hp_neg

namespace ComparisonSet

/--
If $G\ngeq_\mathcal{A}H$, then $G$ and $H$ must be both `LeftSeparating` and
`RightSeparating`. This generalises a result of [Siegel (Lemma 5.8 on p.
214)][siegel:GeneralDeadendingUniverse:2025], which proved it only for short
augmented forms and short universes.
-/
lemma leftSeparating_rightSeparating_of_not_misereGE
    {A : G → Prop} [ComparisonSet A] {g h : G}
    (hg : IsAmbient A g) (hh : IsAmbient A h) (h_not_ge : ¬(g ≥m A h)) :
    LeftSeparating A g h ∧ RightSeparating A g h := by
  exact separating_pair_of_not_misereGE hg hh h_not_ge

/--
If $\nexists G^L$ such that $G^L\ge_\mathcal{A}H$, and $\nexists H^R$ such that
$G\ge_\mathcal{A}H^R$, then $G$ must be downlinked to $H$.

This is a transfinite generalisation of one half of a result of [Siegel (Lemma
5.10 on p. 214)][siegel:GeneralDeadendingUniverse:2025].
-/
lemma downlinked_of_not_exists_moves_misereGE
    {A : G → Prop} [ComparisonSet A] {g h : G}
    (hg : IsAmbient A g) (hh : IsAmbient A h)
    (h_left : ¬∃ gl ∈ moves .left g, gl ≥m A h)
    (h_right : ¬∃ hr ∈ moves .right h, g ≥m A hr) :
    Downlinked A g h := by
  classical
  have h_left_sep :
      ∀ gl : moves .left g, LeftSeparating A (gl : G) h := by
    intro gl
    have h_not_ge : ¬((gl : G) ≥m A h) := by
      intro hge
      exact h_left ⟨gl, gl.prop, hge⟩
    exact (leftSeparating_rightSeparating_of_not_misereGE
      (Hereditary.has_option hg (IsOption.of_mem_moves gl.prop)) hh h_not_ge).left
  have h_right_sep :
      ∀ hr : moves .right h, RightSeparating A g (hr : G) := by
    intro hr
    have h_not_ge : ¬(g ≥m A (hr : G)) := by
      intro hge
      exact h_right ⟨hr, hr.prop, hge⟩
    exact (leftSeparating_rightSeparating_of_not_misereGE
      hg (Hereditary.has_option hh (IsOption.of_mem_moves hr.prop)) h_not_ge).right
  choose x hxA hxLose hxWin using h_left_sep
  choose y hyA hyWin hyLose using h_right_sep
  let L : Set G := downlinkLeftSet g h y
  let R : Set G := downlinkRightSet g h x
  haveI : Small.{u} (downlinkZero .left g h) := by
    by_cases hz : IsEnd .right g ∧ IsEnd .right h
    · simpa [downlinkZero, hz] using (inferInstance : Small.{u} ({0} : Set G))
    · simpa [downlinkZero, hz] using (inferInstance : Small.{u} (∅ : Set G))
  haveI : Small.{u} (downlinkZero .right h g) := by
    by_cases hz : IsEnd .left h ∧ IsEnd .left g
    · simpa [downlinkZero, hz] using (inferInstance : Small.{u} ({0} : Set G))
    · simpa [downlinkZero, hz] using (inferInstance : Small.{u} (∅ : Set G))
  haveI : Small.{u} L := inferInstance
  haveI : Small.{u} R := inferInstance
  have htA : A (downlinkWitness g h x y) :=
    downlinkWitness_mem hg hh hxA hyA
  exact downlinked_of_downlinkWitness_mem htA hxLose hxWin hyWin hyLose

private lemma not_misereGE_of_right_left_outcomes
    {A : G → Prop} {g h t : G} (hge : g ≥m A h) (ht : A t) (p : Player)
    (hgt : MiserePlayerOutcome (g + t) p = .right)
    (hht : MiserePlayerOutcome (h + t) p = .left) : False := by
  have h_cmp := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (hge t ht) p
  rw [hgt, hht] at h_cmp
  exact Player.left_le_right h_cmp

private lemma not_downlinked_left_option_of_misereGE
    {A : G → Prop} {g h hl : G} (hge : g ≥m A h) (hhl : hl ∈ moves .left h) :
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
    {A : G → Prop} {g h gr : G} (hge : g ≥m A h) (hgr : gr ∈ moves .right g) :
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
    {A : G → Prop} [ComparisonSet A] {g h : G} (p : Player)
    (hg : IsAmbient A g) (hh : IsAmbient A h) (hge : g ≥m A h) :
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
    {A : G → Prop} [ComparisonSet A] {g h : G}
    (hg : IsAmbient A g) (hh : IsAmbient A h) :
    g ≥m A h →
      Maintenance A g h .right ∧ Maintenance A g h .left ∧
      Proviso A g h .right ∧ Proviso A h g .left := by
  intro hge
  exact ⟨maintenance_of_misereGE .right hg hh hge,
    maintenance_of_misereGE .left hg hh hge,
    proviso_right_of_misereGE hge,
    proviso_left_of_misereGE hge⟩

end ComparisonSet

end Separation

end Form
