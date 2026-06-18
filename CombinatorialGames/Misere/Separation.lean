/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import CombinatorialGames.Form.Misere.Adjoint
public import CombinatorialGames.Misere.Hereditary.MaintenanceProviso

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

theorem misereGE_iff_not_separating {A : G → Prop} {g h : G} :
    g ≥m A h ↔ ¬ LeftSeparating A g h ∧ ¬ RightSeparating A g h := by
  constructor
  · intro hge
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx, h1, h2⟩
      have hcmp := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (hge x hx) .left
      rw [miserePlayerOutcome_eq_iff_winsGoingFirst.mpr h2] at hcmp
      have hg : MiserePlayerOutcome (g + x) .left = .right := by
        cases hgx : MiserePlayerOutcome (g + x) .left with
        | left => exact absurd (miserePlayerOutcome_eq_iff_winsGoingFirst.mp hgx) h1
        | right => rfl
      rw [hg] at hcmp
      exact Player.left_le_right hcmp
    · rintro ⟨x, hx, h1, h2⟩
      have hcmp := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (hge x hx) .right
      have hh : MiserePlayerOutcome (h + x) .right = .left := by
        cases hhx : MiserePlayerOutcome (h + x) .right with
        | left => rfl
        | right => exact absurd (miserePlayerOutcome_eq_iff_winsGoingFirst.mp hhx) h2
      rw [miserePlayerOutcome_eq_iff_winsGoingFirst.mpr h1, hh] at hcmp
      exact Player.left_le_right hcmp
  · rintro ⟨h1, h2⟩
    by_contra h_not_ge
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
        absurd h1
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
        absurd h2
        cases hg : MiserePlayerOutcome (g + x) .right
        <;> cases hh : MiserePlayerOutcome (h + x) .right
        <;> simp [hg, hh] at h_right
        refine ⟨x, hx, ?_, ?_⟩
        · exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp hg
        · intro h_win
          have h_out := miserePlayerOutcome_eq_iff_winsGoingFirst.mpr h_win
          rw [hh] at h_out
          cases h_out

/--
Negation of `misereGE_iff_not_separating`
-/
theorem not_misereGE_iff_separating {A : G → Prop} {g h : G} :
    ¬(g ≥m A h) ↔ LeftSeparating A g h ∨ RightSeparating A g h := by
  constructor
  · intro h1
    have := misereGE_iff_not_separating.not.mp h1
    exact or_iff_not_and_not.mpr this
  · rintro (h1 | h2)
    · exact misereGE_iff_not_separating.not.mpr (or_iff_not_and_not.mp (Or.inl h1))
    · exact misereGE_iff_not_separating.not.mpr (or_iff_not_and_not.mp (Or.inr h2))

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

lemma downlinked_of_downlinkWitness_mem
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
    have hm_neg : Maintenance A (- -g) (- -h) (- -p) := by simpa only [neg_neg] using hm
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
    have hp_neg : Proviso A (- -g) (- -h) (- -p) := by simpa only [neg_neg] using hp
    simpa using proviso_neg (g := -g) (h := -h) (p := -p) hp_neg

end Separation

end Form
