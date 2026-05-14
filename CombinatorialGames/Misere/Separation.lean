/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import CombinatorialGames.Form.Misere.Adjoint
public import CombinatorialGames.Misere.Hereditary

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
lemma leftSeparating_or_rightSeparating_of_not_misereGE {U : G → Prop}
    {g h : G} (h_not_ge : ¬(g ≥m U h)) :
    LeftSeparating U g h ∨ RightSeparating U g h := by
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
    {U : G → Prop} {g h : G}
    (h_candidate : ∀ {x : G}, U x → U (rightSeparatorCandidate h x))
    (h_left_sep : LeftSeparating U g h) :
    RightSeparating U g h := by
  obtain ⟨x, hx, hgx, hhx⟩ := h_left_sep
  let y := rightSeparatorCandidate h x
  have hy : U y := h_candidate hx
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
      change IsEndLike .right (rightSeparatorCandidate h x) at hy_end
      unfold rightSeparatorCandidate at hy_end
      rw [ofSets_isEndLike_iff
        (s := rightSeparatorLeftSet h) (t := {x}),
        isEnd_def] at hy_end
      rw [rightMoves_ofSets (s := rightSeparatorLeftSet h) (t := {x})] at hy_end
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
This constructs the following game form, which is a trivial generalisation of a
construction by [Siegel (Proof of Lemma 5.10 on p.
215)][siegel:GeneralDeadendingUniverse:2025] for short forms:
$$
T=
\begin{cases}
*
& \text{if neither }G\text{ nor }H\text{ has any ordinary options},\\
\form<0>[(H^\mathcal{L})^\circ]
& \text{if }G\text{ has no ordinary options and }H\text{ has no ordinary Right options},\\
\form<(G^\mathcal{R})^\circ>[0]
& \text{if }H\text{ has no ordinary options and }G\text{ has no ordinary Left options},\\
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
    {U : G → Prop} {g h : G}
    {x : moves .left g → G} {y : moves .right h → G}
    [Small (downlinkLeftSet g h y)] [Small (downlinkRightSet g h x)]
    (htU : U (downlinkWitness g h x y))
    (hxLose : ∀ gl : moves .left g, ¬WinsGoingFirst .left ((gl : G) + x gl))
    (hxWin : ∀ gl : moves .left g, WinsGoingFirst .left (h + x gl))
    (hyWin : ∀ hr : moves .right h, WinsGoingFirst .right (g + y hr))
    (hyLose : ∀ hr : moves .right h, ¬WinsGoingFirst .right ((hr : G) + y hr)) :
    Downlinked U g h := by
  let L := downlinkLeftSet g h y
  let R := downlinkRightSet g h x
  let t : G := !{L | R}
  have hLnonempty : L.Nonempty := downlinkOptions_nonempty .left g h y
  have hRnonempty : R.Nonempty := downlinkOptions_nonempty .right h g x
  change U t at htU
  refine ⟨t, htU, ?_, ?_⟩
  · rw [not_winsGoingFirst_iff]
    constructor
    · intro hEnd
      have htEnd : IsEndLike .left t := (IsEndLike.add_iff.mp hEnd).right
      change IsEndLike .left !{L | R} at htEnd
      rw [ofSets_isEndLike_iff, isEnd_def, leftMoves_ofSets] at htEnd
      exact hLnonempty.ne_empty htEnd
    · intro k hk
      rw [moves_add] at hk
      rcases hk with ⟨gl, hgl, rfl⟩ | ⟨tl, htl, rfl⟩
      · apply winsGoingFirst_of_moves
        refine ⟨gl + x ⟨gl, hgl⟩, ?_, hxLose ⟨gl, hgl⟩⟩
        apply add_left_mem_moves_add
        change x ⟨gl, hgl⟩ ∈ moves .right !{L | R}
        rw [rightMoves_ofSets]
        simp [R, downlinkRightSet]
      · change tl ∈ moves .left !{L | R} at htl
        rw [leftMoves_ofSets] at htl
        simp only [L, downlinkLeftSet, downlinkOptions, downlinkZero, Set.mem_union,
          Set.mem_range] at htl
        rcases htl with (⟨hr, htl_eq⟩ | ⟨gr, htl_eq⟩) | htl_zero
        · rw [← htl_eq]
          exact hyWin hr
        · rw [← htl_eq]
          apply winsGoingFirst_of_moves
          refine ⟨(gr : G) + (gr : G)°, add_right_mem_moves_add gr.prop ((gr : G)°), ?_⟩
          exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P (gr : G))
        · by_cases hz : IsEnd .right g ∧ IsEnd .right h
          · simp [hz] at htl_zero
            rw [htl_zero]
            exact winsGoingFirst_of_isEndLike
              (IsEndLike.add_iff.mpr ⟨isEndLike_of_isEnd hz.left, isEndLike_of_isEnd isEnd_zero⟩)
          · simp [hz] at htl_zero
  · rw [not_winsGoingFirst_iff]
    constructor
    · intro hEnd
      have htEnd : IsEndLike .right t := (IsEndLike.add_iff.mp hEnd).right
      change IsEndLike .right !{L | R} at htEnd
      rw [ofSets_isEndLike_iff, isEnd_def, rightMoves_ofSets] at htEnd
      exact hRnonempty.ne_empty htEnd
    · intro k hk
      rw [moves_add] at hk
      rcases hk with ⟨hr, hhr, rfl⟩ | ⟨tr, htr, rfl⟩
      · apply winsGoingFirst_of_moves
        refine ⟨hr + y ⟨hr, hhr⟩, ?_, hyLose ⟨hr, hhr⟩⟩
        apply add_left_mem_moves_add
        change y ⟨hr, hhr⟩ ∈ moves .left !{L | R}
        rw [leftMoves_ofSets]
        simp [L, downlinkLeftSet]
      · change tr ∈ moves .right !{L | R} at htr
        rw [rightMoves_ofSets] at htr
        simp only [R, downlinkRightSet, downlinkOptions, downlinkZero, Set.mem_union,
          Set.mem_range] at htr
        rcases htr with (⟨gl, htr_eq⟩ | ⟨hl, htr_eq⟩) | htr_zero
        · rw [← htr_eq]
          exact hxWin gl
        · rw [← htr_eq]
          apply winsGoingFirst_of_moves
          refine ⟨(hl : G) + (hl : G)°, add_right_mem_moves_add hl.prop ((hl : G)°), ?_⟩
          exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P (hl : G))
        · by_cases hz : IsEnd .left h ∧ IsEnd .left g
          · simp [hz] at htr_zero
            rw [htr_zero]
            exact winsGoingFirst_of_isEndLike
              (IsEndLike.add_iff.mpr ⟨isEndLike_of_isEnd hz.left, isEndLike_of_isEnd isEnd_zero⟩)
          · simp [hz] at htr_zero

end Separation

/--
If $G$ and $H$ are `RightSeparating`, then $\overline{H}$ and $\overline{G}$
must be `LeftSeparating`.
-/
lemma leftSeparating_neg_of_rightSeparating {U : G → Prop} [ClosedUnderNeg U]
    {g h : G} (h_right_sep : RightSeparating U g h) :
    LeftSeparating U (-h) (-g) := by
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
lemma leftSeparating_of_rightSeparating_neg {U : G → Prop} [ClosedUnderNeg U]
    {g h : G} (h_right_sep : RightSeparating U (-h) (-g)) :
    LeftSeparating U g h := by
  simpa using (leftSeparating_neg_of_rightSeparating h_right_sep)

namespace Separation

/--
This is an interface used to show that $G\ge_\mathcal{U}H$ implies
`Form.Maintenance` and `Form.Proviso` (see `maintenance_proviso_of_misereGE`)
for both `Universe` and `ShortUniverse` simultaneously.

The `Legal` predicate dictates what game forms are admissible for comparison
modulo the set. For example, in a `ShortUniverse`, we would write `Legal :=
IsShort`. We require the set of legal forms to be hereditary and closed
under conjugation. The final two fields assert that our separating and downlink
constructions are always elements of `A`.
-/
class ComparisonSet (A : G → Prop) extends ClosedUnderNeg A where
  Legal : G → Prop
  legal_moves {g g' : G} {p : Player} : Legal g → g' ∈ moves p g → Legal g'
  legal_neg {g : G} : Legal g → Legal (-g)
  rightSeparatorCandidate_mem {h x : G} :
    Legal h → A x → A (rightSeparatorCandidate h x)
  downlinkWitness_mem {g h : G} {x : moves .left g → G} {y : moves .right h → G}
    [Small (downlinkLeftSet g h y)] [Small (downlinkRightSet g h x)] :
    Legal g → Legal h → (∀ gl, A (x gl)) → (∀ hr, A (y hr)) →
      A (downlinkWitness g h x y)

-- TODO: move this elsewhere
private theorem maintenance_neg
    {U : G → Prop} [ClosedUnderNeg U] {g h : G} {p : Player}
    (h_maintenance : Maintenance U (-h) (-g) (-p)) :
    Maintenance U g h p := by
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
    {U : G → Prop} [ClosedUnderNeg U] {g h : G} (p : Player) :
    Maintenance U (-h) (-g) (-p) ↔ Maintenance U g h p := by
  constructor
  · exact maintenance_neg
  · intro hm
    have hm_neg : Maintenance U (- -g) (- -h) (- -p) := by simpa using hm
    simpa using maintenance_neg (g := -h) (h := -g) (p := -p) hm_neg

-- TODO: move this elsewhere
private theorem proviso_neg
    {U : G → Prop} [ClosedUnderNeg U] {g h : G} {p : Player}
    (h_proviso : Proviso U (-g) (-h) (-p)) :
    Proviso U g h p := by
  intro hg_end x hx hx_end
  have hwin_neg : WinsGoingFirst (-p) ((-h) + (-x)) :=
    h_proviso (by simpa [IsEndLike.neg_iff_neg] using hg_end)
      (-x) (ClosedUnderNeg.neg_of hx)
      (by simpa [IsEndLike.neg_iff_neg] using hx_end)
  rw [← winsGoingFirst_neg_iff, neg_add_rev, neg_neg, neg_neg, add_comm] at hwin_neg
  exact hwin_neg

-- TODO: move this elsewhere
theorem proviso_neg_iff
    {U : G → Prop} [ClosedUnderNeg U] {g h : G} (p : Player) :
    Proviso U (-g) (-h) (-p) ↔ Proviso U g h p := by
  constructor
  · exact proviso_neg
  · intro hp
    have hp_neg : Proviso U (- -g) (- -h) (- -p) := by simpa using hp
    simpa using proviso_neg (g := -g) (h := -h) (p := -p) hp_neg

namespace ComparisonSet

/-
Note the discrepancy in hypotheses with the analogous
`leftSeparating_of_rightSeparating_not_misereGE`; this is due to the additional
one-sided structure imposed on `ComparisonSet`.
-/
private lemma rightSeparating_of_leftSeparating
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hh : Legal U h)
    (h_left_sep : LeftSeparating U g h) :
    RightSeparating U g h := by
  refine rightSeparating_of_leftSeparating_of_rightSeparatorCandidate_mem ?_ h_left_sep
  intro x hx
  exact rightSeparatorCandidate_mem hh hx

/-
If $G\ngeq_\mathcal{U}H$, and $G$ and $H$ are `RightSeparating`, then they must
also be `LeftSeparating`.
-/
private lemma leftSeparating_of_rightSeparating_not_misereGE
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hg : Legal U g)
    (h_not_ge : ¬(g ≥m U h))
    (h_right_sep : RightSeparating U g h) :
    LeftSeparating U g h := by
  have h_not_ge_neg : ¬((-h) ≥m U (-g)) := by
    rwa [ClosedUnderNeg.neg_ge_neg_iff]
  have h_left_sep_neg : LeftSeparating U (-h) (-g) :=
    leftSeparating_neg_of_rightSeparating h_right_sep
  have h_right_sep_neg : RightSeparating U (-h) (-g) :=
    rightSeparating_of_leftSeparating
      (legal_neg hg) h_left_sep_neg
  exact leftSeparating_of_rightSeparating_neg h_right_sep_neg

/--
If $G\ngeq_\mathcal{U}H$, then $G$ and $H$ must be both `LeftSeparating` and
`RightSeparating`. This generalises a result of [Siegel (Lemma 5.8 on p.
214)][siegel:GeneralDeadendingUniverse:2025], which proved it only for short
augmented forms and short universes.
-/
lemma leftSeparating_rightSeparating_of_not_misereGE
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hg : Legal U g) (hh : Legal U h) (h_not_ge : ¬(g ≥m U h)) :
    LeftSeparating U g h ∧ RightSeparating U g h := by
  cases leftSeparating_or_rightSeparating_of_not_misereGE h_not_ge with
  | inl h_left =>
      exact ⟨h_left, rightSeparating_of_leftSeparating
        hh h_left⟩
  | inr h_right =>
      exact ⟨leftSeparating_of_rightSeparating_not_misereGE
        hg h_not_ge h_right, h_right⟩

/--
If $\nexists G^L$ such that $G^L\ge_\mathcal{U}H$, and $\nexists H^R$ such that
$G\ge_\mathcal{U}H^R$, then $G$ must be downlinked to $H$.

This is a transfinite generalisation of one half of a result of [Siegel (Lemma
5.10 on p. 214)][siegel:GeneralDeadendingUniverse:2025].
-/
lemma downlinked_of_not_exists_moves_misereGE
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hg : Legal U g) (hh : Legal U h)
    (h_left : ¬∃ gl ∈ moves .left g, gl ≥m U h)
    (h_right : ¬∃ hr ∈ moves .right h, g ≥m U hr) :
    Downlinked U g h := by
  classical
  have h_left_sep :
      ∀ gl : moves .left g, LeftSeparating U (gl : G) h := by
    intro gl
    have h_not_ge : ¬((gl : G) ≥m U h) := by
      intro hge
      exact h_left ⟨gl, gl.prop, hge⟩
    exact (leftSeparating_rightSeparating_of_not_misereGE
      (legal_moves hg gl.prop) hh h_not_ge).left
  have h_right_sep :
      ∀ hr : moves .right h, RightSeparating U g (hr : G) := by
    intro hr
    have h_not_ge : ¬(g ≥m U (hr : G)) := by
      intro hge
      exact h_right ⟨hr, hr.prop, hge⟩
    exact (leftSeparating_rightSeparating_of_not_misereGE
      hg (legal_moves hh hr.prop) h_not_ge).right
  choose x hxU hxLose hxWin using h_left_sep
  choose y hyU hyWin hyLose using h_right_sep
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
  have htU : U (downlinkWitness g h x y) :=
    downlinkWitness_mem hg hh hxU hyU
  exact downlinked_of_downlinkWitness_mem htU hxLose hxWin hyWin hyLose

private lemma maintenance_right_of_misereGE
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hg : Legal U g) (hh : Legal U h) (hge : g ≥m U h) :
    Maintenance U g h .right := by
  intro gr hgr
  by_contra h_not
  have h_downlinked : Downlinked U gr h := by
    apply downlinked_of_not_exists_moves_misereGE (legal_moves hg hgr) hh
    · intro h_exists
      exact h_not (Or.inr h_exists)
    · intro h_exists
      exact h_not (Or.inl h_exists)
  obtain ⟨t, ht, hgrt, hht⟩ := h_downlinked
  have hgrt_out : MiserePlayerOutcome (gr + t) .left = .right := by
    unfold MiserePlayerOutcome
    simp [hgrt]
  have hgt : MiserePlayerOutcome (g + t) .right = .right :=
    miserePlayerOutcome_of_rightMoves (add_right_mem_moves_add hgr t) hgrt_out
  have hht_out : MiserePlayerOutcome (h + t) .right = .left := by
    unfold MiserePlayerOutcome
    simp [hht]
  have h_cmp := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (hge t ht) .right
  rw [hgt, hht_out] at h_cmp
  exact Player.left_le_right h_cmp

private lemma maintenance_left_of_misereGE
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hg : Legal U g) (hh : Legal U h) (hge : g ≥m U h) :
    Maintenance U g h .left := by
  have hge_neg : (-h) ≥m U (-g) :=
    (ClosedUnderNeg.neg_ge_neg_iff g h).mpr hge
  exact (maintenance_neg_iff .left).mp
    (maintenance_right_of_misereGE (legal_neg hh) (legal_neg hg) hge_neg)

/--
If $G\ge_\mathcal{U}H$, then $G$ and $H$ must satisfy both the
`Form.Maintenance` and the `Form.Proviso`.
-/
theorem maintenance_proviso_of_misereGE
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hg : Legal U g) (hh : Legal U h) :
    g ≥m U h →
      Maintenance U g h .right ∧ Maintenance U g h .left ∧
      Proviso U g h .right ∧ Proviso U h g .left := by
  intro hge
  exact ⟨maintenance_right_of_misereGE hg hh hge,
    maintenance_left_of_misereGE hg hh hge,
    proviso_right_of_misereGE hge,
    proviso_left_of_misereGE hge⟩

end ComparisonSet

end Separation

end Form
