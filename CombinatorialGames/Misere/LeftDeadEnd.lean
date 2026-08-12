/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.DeadEnding
public import CombinatorialGames.Misere.NonInvertible
public import CombinatorialGames.Misere.Quotients
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.List

/-! # Left Dead Ends -/

universe u

open Form
open Form.DeadEnding
open Form.Misere.Outcome

public noncomputable section

namespace GameForm.LeftDeadEnd

/-! ## The basic theory -/

/-! ### Core predicate, ambient universe, notation -/

@[expose] def IsLde (g : GameForm) : Prop := IsShort g ∧ IsDeadEnd .left g

/-- Comparison of Left dead ends is multiversal, so we fix the dead-ending universe
$\mathcal{E}$ as the ambient set, writing $G \ge H$ for $G \ge_{\mathcal{E}} H$ and $G = H$
for $G =_{\mathcal{E}} H$. -/
scoped notation:50 g:50 " ≥ₗ " h:51 => MisereGE (Form.DeadEnding.ShortDeadEnding) g h
scoped notation:50 g:50 " ≡ₗ " h:51 => MisereEQ (Form.DeadEnding.ShortDeadEnding) g h

theorem isLde_zero : IsLde 0 := ⟨IsShort.zero, isDeadEnd_zero⟩

theorem IsLde.short {g : GameForm} (h : IsLde g) : IsShort g := h.1

theorem IsLde.deadEnd {g : GameForm} (h : IsLde g) : IsDeadEnd .left g := h.2

theorem IsLde.add {g h : GameForm} (hg : IsLde g) (hh : IsLde h) : IsLde (g + h) :=
  ⟨IsShort.add hg.short hh.short, IsDeadEnd.add hg.deadEnd hh.deadEnd⟩

theorem isLde_sum {s : Multiset GameForm} (hs : ∀ a ∈ s, IsLde a) : IsLde s.sum := by
  induction s using Multiset.induction_on with
  | empty => simpa using isLde_zero
  | cons a s ih =>
    rw [Multiset.sum_cons]
    exact (hs a (Multiset.mem_cons_self a s)).add
      (ih fun b hb => hs b (Multiset.mem_cons_of_mem hb))

theorem IsLde.of_mem_rightMoves {g gr : GameForm} (hg : IsLde g) (h : gr ∈ moves .right g) :
    IsLde gr :=
  ⟨IsShort.of_mem_moves hg.short h, isDeadEnd_of_mem_moves hg.deadEnd h⟩

theorem IsDeadEnd.isDeadEnding {g : GameForm} (hg : IsDeadEnd .left g) : IsDeadEnding g := by
  unfold IsDeadEnding
  refine ⟨fun p hp => ?_, fun p gp hgp => ?_⟩
  · cases p
    · exact hg
    · rw [GameForm.both_ends_eq_zero (isEnd_of_isDeadEnd hg) hp]
      exact isDeadEnd_zero
  · cases p
    · exact absurd hgp (by simp [isEnd_of_isDeadEnd hg])
    · exact IsDeadEnd.isDeadEnding (IsDeadEnd.hereditary_def hg gp hgp)
termination_by g
decreasing_by form_wf

theorem IsLde.shortDeadEnding {g : GameForm} (hg : IsLde g) : ShortDeadEnding g :=
  ⟨hg.short, IsDeadEnd.isDeadEnding hg.deadEnd⟩

theorem IsLde.rightMoves_nonempty {g : GameForm} (hg : IsLde g) (hne : g ≠ 0) :
    (moves .right g).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h_empty
  exact hne (GameForm.both_ends_eq_zero (isEnd_of_isDeadEnd hg.deadEnd)
    (by rw [isEnd_def]; exact h_empty))

theorem isLde_neg_intCast (n : ℕ) : IsLde (-(n : GameForm)) := by
  refine ⟨IsShort.neg (IsShort.natCast n), ?_⟩
  rw [← Form.intCast_nat n, ← Form.intCast_neg]
  exact isDeadEnd_left_nonpos_intCast (-(n : ℤ)) (by simp)

theorem isLde_neg_one : IsLde (-(1 : GameForm)) := by
  have h := isLde_neg_intCast 1
  rwa [Nat.cast_one] at h

theorem rightMoves_neg_one : moves .right (-(1 : GameForm)) = {(0 : GameForm)} := by
  simp [moves_neg]

theorem rightMoves_neg_intCast_succ (n : ℕ) :
    moves .right (-((n + 1 : ℕ) : GameForm)) = {-(n : GameForm)} := by
  rw [Nat.cast_add_one, moves_neg]
  simp [leftMoves_natCast_succ]

theorem leftMoves_neg_intCast (n : ℕ) :
    moves .left (-(n : GameForm)) = (∅ : Set GameForm) := by
  simp [moves_neg]

theorem leftMoves_neg_one : moves .left (-(1 : GameForm)) = (∅ : Set GameForm) := by
  simp [moves_neg]

@[expose] def waitingGame : ℕ → GameForm
  | 0 => 0
  | (n + 1) => !{(∅ : Set GameForm) | {0, waitingGame n}}

theorem isLde_waitingGame (n : ℕ) : IsLde (waitingGame n) := by
  induction n with
  | zero => exact isLde_zero
  | succ n ih =>
    rw [waitingGame]
    refine ⟨IsShort.ofSets Set.finite_empty (by simp) ((Set.finite_singleton _).insert _) ?_, ?_⟩
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact IsShort.zero
      · exact ih.short
    · rw [isDeadEnd_def]
      refine ⟨by rw [isEnd_def]; simp, fun gp hgp => ?_⟩
      rw [moves_ofSets] at hgp
      simp only [Player.cases, Set.mem_insert_iff, Set.mem_singleton_iff] at hgp
      rcases hgp with rfl | rfl
      · exact isDeadEnd_zero
      · exact ih.deadEnd

theorem rightMoves_waitingGame (n : ℕ) :
    moves .right (waitingGame (n + 1)) = {0, waitingGame n} := by
  rw [waitingGame]
  simp

theorem waitingGame_succ_ne_zero (n : ℕ) : waitingGame (n + 1) ≠ 0 := by
  intro hc
  have h := rightMoves_waitingGame n
  rw [hc, moves_zero] at h
  exact absurd (h ▸ Set.mem_insert (0 : GameForm) _) (Set.notMem_empty _)

private theorem lde_promain : Promain (IsShort (G := GameForm)) ShortDeadEnding :=
  @Promain.of_universe GameForm (inferInstance : Form GameForm) IsShort ShortDeadEnding
    instAmbientIsShort inferInstance

/--
If $\mathcal{U}$ is a universe, and $G$ and $H$ are Left dead ends, then $G \ge_{\mathcal{U}} H$
if and only if the following hold:

1. if $G \cong 0$, then $H \cong 0$; otherwise,

2. for every $G^R \in G^{\mathcal{R}}$, there exists some $H^R \in H^{\mathcal{R}}$ such that
   $G^R \ge_{\mathcal{U}} H^R$.

This is [Davies (Theorem 2.4 on p. 7)][davies:FactorisationsLeftDead:2024].
-/
theorem misereGE_lde_iff {g h : GameForm} (hg : IsLde g) (hh : IsLde h) :
    (g ≥ₗ h) ↔
      (IsEnd .right g → IsEnd .right h) ∧
      (∀ gr ∈ moves .right g, ∃ hr ∈ moves .right h, gr ≥ₗ hr) := by
  rw [misereGE_iff_isEndLike_of_isDeadEnd_left lde_promain
    ⟨0, Universe.zero_mem IsShort, isEnd_zero, isEnd_zero⟩
    hg.deadEnd hh.deadEnd hg.short hh.short]
  simp only [isEndLike_iff_isEnd]

-- TODO: [Davies (Corollary 2.5 on p. 7)][davies:FactorisationsLeftDead:2024]

/-! ### Runs -/

@[expose] def IsRun : List GameForm → Prop
  | [] => False
  | [_] => True
  | (a :: b :: l) => b ∈ moves .right a ∧ IsRun (b :: l)

theorem IsLde.of_mem_isRun {g : GameForm} (hg : IsLde g) {l : List GameForm}
    (hl : IsRun (g :: l)) : ∀ x ∈ g :: l, IsLde x := by
  induction l generalizing g with
  | nil =>
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact hg
  | cons b l ih =>
    obtain ⟨hb_mem, hb_run⟩ := hl
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hg
    · exact ih (hg.of_mem_rightMoves hb_mem) hb_run x hx'

/--
If $G$ and $H$ are Left dead ends with $G \ge H$, and $k$ is an integer satisfying
$0 \le k \le \tilde{b}(G)$, then, for any run $(G_0, G_1, \ldots, G_k)$ of $G$ of length $k$,
there exists a run $(H_0, H_1, \ldots, H_k)$ of $H$ of length $k$ such that $G_i \ge H_i$ for
every $0 \le i \le k$.

This is [Davies (Corollary 3.2 on p. 10)][davies:FactorisationsLeftDead:2024].
-/
theorem exists_run_dominated {g h : GameForm} (hg : IsLde g) (hh : IsLde h) (hge : g ≥ₗ h)
    {l : List GameForm} (hl : IsRun (g :: l)) :
    ∃ m : List GameForm, IsRun (h :: m) ∧ List.Forall₂ (fun a b => a ≥ₗ b) (g :: l) (h :: m) := by
  induction l generalizing g h with
  | nil => exact ⟨[], trivial, List.Forall₂.cons hge List.Forall₂.nil⟩
  | cons b l ih =>
    obtain ⟨hb_mem, hb_run⟩ := hl
    obtain ⟨hr, hhr_mem, hb_ge⟩ := ((misereGE_lde_iff hg hh).mp hge).2 b hb_mem
    obtain ⟨m, hm_run, hm_rel⟩ := ih (hg.of_mem_rightMoves hb_mem) (hh.of_mem_rightMoves hhr_mem)
      hb_ge hb_run
    exact ⟨hr :: m, ⟨hhr_mem, hm_run⟩, List.Forall₂.cons hge hm_rel⟩

/-! ### Good options -/

@[expose] def LdeGt (a b : GameForm) : Prop := (a ≥ₗ b) ∧ ¬(b ≥ₗ a)

/--
If $G$ is a combinatorial game, then we will say that a (Left, respectively Right) option $G'$
of $G$ is *good* if it is not strictly dominated by another (Left, respectively Right) option of
$G$.

This is [Davies (Definition 3.3 on p. 11)][davies:FactorisationsLeftDead:2024].
-/
@[expose] def IsGoodOption (gr g : GameForm) : Prop :=
  gr ∈ moves .right g ∧ ¬ ∃ gr' ∈ moves .right g, LdeGt gr gr'

theorem exists_isGoodOption_le_of_mem_rightMoves {g x : GameForm} (hg : IsLde g)
    (hx : x ∈ moves .right g) : ∃ gr, IsGoodOption gr g ∧ x ≥ₗ gr := by
  by_cases hgood : IsGoodOption x g
  · exact ⟨x, hgood, MisereGE.refl x⟩
  · have hgood' : ∃ x' ∈ moves .right g, LdeGt x x' := by
      by_contra hc
      exact hgood ⟨hx, hc⟩
    obtain ⟨x', hx'_mem, hx'_ge, hx'_ndom⟩ := hgood'
    obtain ⟨gr, hgr_good, hgr_le⟩ := exists_isGoodOption_le_of_mem_rightMoves hg hx'_mem
    exact ⟨gr, hgr_good, hx'_ge.trans hgr_le⟩
termination_by Set.ncard {z ∈ moves .right g | x ≥ₗ z} -- TODO: No tactic can do it?
decreasing_by
  have h_fin : (moves .right g).Finite := IsShort.finite_moves .right hg.short
  refine Set.ncard_lt_ncard ⟨fun z hz => ⟨hz.1, hx'_ge.trans hz.2⟩, fun h_sub => ?_⟩
    (h_fin.subset fun z hz => hz.1)
  exact hx'_ndom (h_sub ⟨hx, MisereGE.refl x⟩).2

/--
If $G \ge H$ and $G^R$ is a good option of $G$, then some (good) option $H^R$ of $H$ has
$G^R \ge H^R$.

This is the $\ge$ case of [Davies (Corollary 3.4 on p. 11)][davies:FactorisationsLeftDead:2024].
-/
theorem lde_good_option_dominates {g h gr : GameForm} (hg : IsLde g) (hh : IsLde h)
    (hge : g ≥ₗ h) (hgr : IsGoodOption gr g) :
    ∃ hr, IsGoodOption hr h ∧ (gr ≥ₗ hr) := by
  obtain ⟨hr'', hhr''_mem, hge_hr''⟩ := ((misereGE_lde_iff hg hh).mp hge).2 gr hgr.1
  obtain ⟨hr, hhr_good, hhr''_ge_hr⟩ := exists_isGoodOption_le_of_mem_rightMoves hh hhr''_mem
  exact ⟨hr, hhr_good, hge_hr''.trans hhr''_ge_hr⟩

/--
If $G = H$ and $G^R$ is a good option of $G$, then some (good) option $H^R$ of $H$ has
$G^R = H^R$.

This is the $=$ case of [Davies (Corollary 3.4 on p. 11)][davies:FactorisationsLeftDead:2024].
-/
theorem lde_good_option_misereEQ {g h gr : GameForm} (hg : IsLde g) (hh : IsLde h)
    (heq : g ≡ₗ h) (hgr : IsGoodOption gr g) :
    ∃ hr, IsGoodOption hr h ∧ (gr ≡ₗ hr) := by
  obtain ⟨hr, hhr_good, hge⟩ :=
    lde_good_option_dominates hg hh (misereGE_of_misereEQ heq) hgr
  obtain ⟨gr', hgr'_good, hge'⟩ :=
    lde_good_option_dominates hh hg (misereGE_of_misereEQ heq.symm) hhr_good
  have hle : gr' ≥ₗ gr := by
    by_contra hc
    exact hgr.2 ⟨gr', hgr'_good.1, hge.trans hge', hc⟩
  exact ⟨hr, hhr_good, MisereEq.of_antisymm hge (hge'.trans hle)⟩

@[expose] def HasUniqueGoodOption (g : GameForm) : Prop :=
  ∃ gr, IsGoodOption gr g ∧ ∀ gr', IsGoodOption gr' g → gr' ≡ₗ gr

theorem hasUniqueGoodOption_or_multi {g : GameForm} (hg : IsLde g) (hg0 : g ≠ 0) :
    HasUniqueGoodOption g ∨ ∃ a b, IsGoodOption a g ∧ IsGoodOption b g ∧ ¬ (a ≡ₗ b) := by
  by_cases hmulti : ∃ a b, IsGoodOption a g ∧ IsGoodOption b g ∧ ¬ (a ≡ₗ b)
  · exact Or.inr hmulti
  · push_neg at hmulti
    obtain ⟨w₀, hw₀⟩ := hg.rightMoves_nonempty hg0
    obtain ⟨w, hw_good, -⟩ := exists_isGoodOption_le_of_mem_rightMoves hg hw₀
    exact Or.inl ⟨w, hw_good, fun gr' hgr' => hmulti gr' w hgr' hw_good⟩

/--
The monoid of Left dead ends $\mathcal{L}$ is reduced.

This is [Davies (Theorem 3.1 on p. 10)][davies:FactorisationsLeftDead:2024].
-/
theorem lde_misereEQ_zero_iff {g : GameForm} (hg : IsLde g) : (g ≡ₗ 0) ↔ g = 0 := by
  constructor
  · intro heq
    by_contra hne
    have h_out_g := GameForm.DeadEnding.isDeadEnd_left_misereOutcome_L g hne hg.deadEnd
    have h_out_0 := heq 0 (Universe.zero_mem IsShort)
    simp only [add_zero, misereOutcome_zero_N, h_out_g] at h_out_0
    exact absurd h_out_0 (by decide)
  · intro h
    subst h
    intro x hx
    simp

/-! ## Terminal lengths, race and birthday -/

open Classical in
/--
If $G$ is a short game, then we define the set of *terminal lengths* of $G$, denoted
$T(G)$, as the set of all $n$ such that there exists a terminal run of $G$ of length $n$.

This is [Davies (Definition 3.12 on p. 14)][davies:FactorisationsLeftDead:2024], taken
here in the equivalent recursive form of Lemma 3.13.
-/
@[expose] def terminalLengths (g : GameForm) : Set ℕ :=
  if g = 0 then {0} else ⋃ gr ∈ moves .right g, (· + 1) '' terminalLengths gr
termination_by g
decreasing_by form_wf

theorem terminalLengths_zero : terminalLengths 0 = {0} := by
  rw [terminalLengths, if_pos rfl]

/--
If $G$ is a non-zero Left dead end, then $T(G) = \bigcup (T(G') + 1)$, where $G'$ ranges
over all options of $G$.

This is [Davies (Lemma 3.13 on p. 14)][davies:FactorisationsLeftDead:2024].
-/
theorem terminalLengths_of_ne_zero {g : GameForm} (hne : g ≠ 0) :
    terminalLengths g = ⋃ gr ∈ moves .right g, (· + 1) '' terminalLengths gr := by
  rw [terminalLengths, if_neg hne]

theorem terminalLengths_finite_nonempty {g : GameForm} (hg : IsLde g) :
    (terminalLengths g).Finite ∧ (terminalLengths g).Nonempty := by
  by_cases hg0 : g = 0
  · subst hg0
    rw [terminalLengths_zero]
    exact ⟨Set.finite_singleton 0, Set.singleton_nonempty 0⟩
  · rw [terminalLengths_of_ne_zero hg0]
    have h_finite_moves : (moves .right g).Finite := IsShort.finite_moves .right hg.short
    have h_ne_moves : (moves .right g).Nonempty := hg.rightMoves_nonempty hg0
    refine ⟨Set.Finite.biUnion h_finite_moves fun gr hgr => ?_,
      let ⟨gr, hgr⟩ := h_ne_moves
      Set.Nonempty.mono (Set.subset_biUnion_of_mem hgr)
        ((terminalLengths_finite_nonempty (hg.of_mem_rightMoves hgr)).2.image _)⟩
    exact ((terminalLengths_finite_nonempty (hg.of_mem_rightMoves hgr)).1.image _)
termination_by g
decreasing_by form_wf

/--
If $G$ is a short game, define the *race* of $G$, denoted $r(G)$, as
$r(G) := \min(T(G))$.

This is [Davies (Definition 3.14 on p. 15)][davies:FactorisationsLeftDead:2024].
-/
@[expose] def race (g : GameForm) : ℕ := sInf (terminalLengths g)

/--
A Left dead end is an *integer* if it is isomorphic either to $0 := \{\cdot \mid \cdot\}$
or to $\overline{n} := \{\cdot \mid \overline{n - 1}\}$ for some $n \ge 1$ (where
$\overline{0} := 0$).

This is [Davies (p. 15)][davies:FactorisationsLeftDead:2024].
-/
@[expose] def IsInteger (g : GameForm) : Prop := ∃ n : ℤ, g = (n : GameForm)

open Classical in
/--
If $G$ is a Left dead end, then we define the *flexibility* of $G$, written $f(G)$,
recursively as $f(G) = 1 + \max(f(G'))$, where $G'$ ranges over all options of $G$, when
$G$ is not an integer, and as $f(G) := 0$ otherwise.

This is [Davies (Definition 5.1 on p. 22)][davies:FactorisationsLeftDead:2024].
-/
@[expose] def flexibility (g : GameForm) : ℕ :=
  if IsInteger g then 0 else 1 + ⨆ gr : ↥(moves .right g), flexibility gr.1
termination_by g
decreasing_by form_wf

theorem flexibility_of_isInteger {g : GameForm} (hg : IsInteger g) : flexibility g = 0 := by
  rw [flexibility, if_pos hg]

theorem flexibility_of_not_isInteger {g : GameForm} (hne : ¬ IsInteger g) :
    flexibility g = 1 + sSup ((fun gr => flexibility gr) '' moves .right g) := by
  rw [flexibility, if_neg hne, sSup_image']

theorem flexibility_succ_le_of_mem_rightMoves {g gr : GameForm} (hg : IsLde g)
    (hgi : ¬ IsInteger g) (hgr : gr ∈ moves .right g) : flexibility gr + 1 ≤ flexibility g := by
  have h_fin : ((fun x => flexibility x) '' moves .right g).Finite :=
    (IsShort.finite_moves .right hg.short).image _
  have h_le : flexibility gr ≤ sSup ((fun x => flexibility x) '' moves .right g) :=
    le_csSup h_fin.bddAbove (Set.mem_image_of_mem _ hgr)
  rw [flexibility_of_not_isInteger hgi]
  omega

theorem terminalLengths_neg_intCast (n : ℕ) : terminalLengths (-(n : GameForm)) = {n} := by
  induction n with
  | zero => simpa using terminalLengths_zero
  | succ n ih =>
    have hne : -((n + 1 : ℕ) : GameForm) ≠ 0 := by
      intro hc
      have h_ne_empty := rightMoves_neg_intCast_succ n
      rw [hc] at h_ne_empty
      simp at h_ne_empty
    rw [terminalLengths_of_ne_zero hne, rightMoves_neg_intCast_succ]
    simp [ih]

theorem exists_eq_neg_intCast_of_isInteger {g : GameForm} (hg : IsLde g) (hi : IsInteger g) :
    ∃ n : ℕ, g = -(n : GameForm) := by
  obtain ⟨n, rfl⟩ := hi
  have h_left : moves .left ((n : ℤ) : GameForm) = ∅ := by
    rw [← isEnd_def]
    exact isEnd_of_isDeadEnd hg.deadEnd
  have hn : n ≤ 0 := by
    by_contra h_pos
    push_neg at h_pos
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = ((m + 1 : ℕ) : ℤ) := ⟨(n - 1).toNat, by push_cast; omega⟩
    rw [hm, Form.intCast_nat, Nat.cast_add_one, leftMoves_natCast_succ] at h_left
    exact absurd h_left (Set.singleton_ne_empty _)
  refine ⟨n.natAbs, ?_⟩
  rw [← Form.intCast_nat n.natAbs, ← Form.intCast_neg]
  congr 1
  omega

/--
A Left dead end $G$ is an integer if and only if $|T(G)| = 1$. In particular,
$G = \overline{n}$ if and only if $T(G) = \{n\}$.

This is [Davies (Lemma 3.15 on p. 15)][davies:FactorisationsLeftDead:2024].
-/
theorem isInteger_iff_terminalLengths_subsingleton {g : GameForm} (hg : IsLde g) :
    IsInteger g ↔ (terminalLengths g).Subsingleton := by
  constructor
  · intro hi
    obtain ⟨n, rfl⟩ := exists_eq_neg_intCast_of_isInteger hg hi
    rw [terminalLengths_neg_intCast]
    exact Set.subsingleton_singleton
  · intro h_sub
    by_cases hg0 : g = 0
    · exact ⟨0, by rw [hg0, Form.intCast_zero]⟩
    obtain ⟨m, hm_mem⟩ := (terminalLengths_finite_nonempty hg).2
    have h_opt : ∀ gr ∈ moves .right g, gr = -((m - 1 : ℕ) : GameForm) := by
      intro gr hgr_mem
      have hgr_lde := hg.of_mem_rightMoves hgr_mem
      have h_shift : ∀ t ∈ terminalLengths gr, t + 1 = m := by
        intro t ht
        refine h_sub ?_ hm_mem
        rw [terminalLengths_of_ne_zero hg0]
        simp only [Set.mem_iUnion, Set.mem_image]
        exact ⟨gr, hgr_mem, t, ht, rfl⟩
      have h_sub_gr : (terminalLengths gr).Subsingleton := by
        intro a ha b hb
        have h_a := h_shift a ha
        have h_b := h_shift b hb
        omega
      obtain ⟨k, rfl⟩ := exists_eq_neg_intCast_of_isInteger hgr_lde
        ((isInteger_iff_terminalLengths_subsingleton hgr_lde).mpr h_sub_gr)
      have h_k := h_shift k (by rw [terminalLengths_neg_intCast]; rfl)
      rw [show m - 1 = k by omega]
    obtain ⟨gr0, hgr0_mem⟩ := hg.rightMoves_nonempty hg0
    have hm_pos : 1 ≤ m := by
      have hm_mem' := hm_mem
      rw [terminalLengths_of_ne_zero hg0] at hm_mem'
      simp only [Set.mem_iUnion, Set.mem_image] at hm_mem'
      obtain ⟨_, _, t, _, ht_eq⟩ := hm_mem'
      omega
    have h_eq : g = -(m : GameForm) := by
      refine GameForm.ext fun p => ?_
      cases p
      · rw [leftMoves_neg_intCast, ← isEnd_def]
        exact isEnd_of_isDeadEnd hg.deadEnd
      · rw [show m = (m - 1) + 1 by omega, rightMoves_neg_intCast_succ]
        exact Set.eq_singleton_iff_unique_mem.mpr
          ⟨h_opt gr0 hgr0_mem ▸ hgr0_mem, fun x hx => h_opt x hx⟩
    rw [h_eq, ← Form.intCast_nat m, ← Form.intCast_neg]
    exact ⟨-(m : ℤ), rfl⟩
termination_by g
decreasing_by form_wf

/-- See `lde_zero_tfae`. -/
theorem lde_race_zero_iff {g : GameForm} (hg : IsLde g) : race g = 0 ↔ g = 0 := by
  constructor
  · intro hr
    by_contra hne
    have h0_mem : (0 : ℕ) ∈ terminalLengths g :=
      hr ▸ Nat.sInf_mem (terminalLengths_finite_nonempty hg).2
    rw [terminalLengths_of_ne_zero hne] at h0_mem
    simp only [Set.mem_iUnion, Set.mem_image] at h0_mem
    obtain ⟨gr, hgr_mem, t, ht_mem, ht_eq⟩ := h0_mem
    omega
  · intro hg0
    subst hg0
    rw [race, terminalLengths_zero]
    simp

theorem race_le_succ_race_of_mem_rightMoves {g gr : GameForm} (hg : IsLde g)
    (hgr : gr ∈ moves .right g) : race g ≤ race gr + 1 := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact absurd hgr (by simp)
  refine Nat.sInf_le ?_
  rw [terminalLengths_of_ne_zero hg0]
  simp only [Set.mem_iUnion, Set.mem_image]
  exact ⟨gr, hgr, race gr,
    Nat.sInf_mem (terminalLengths_finite_nonempty (hg.of_mem_rightMoves hgr)).2, rfl⟩

theorem exists_mem_rightMoves_race_succ {g : GameForm} (hg : IsLde g) (hg0 : g ≠ 0) :
    ∃ gr ∈ moves .right g, race g = race gr + 1 := by
  have h_mem : race g ∈ terminalLengths g := Nat.sInf_mem (terminalLengths_finite_nonempty hg).2
  rw [terminalLengths_of_ne_zero hg0] at h_mem
  simp only [Set.mem_iUnion, Set.mem_image] at h_mem
  obtain ⟨gr, hgr_mem, t, ht_mem, ht_eq⟩ := h_mem
  have h1 : race gr ≤ t := Nat.sInf_le ht_mem
  have h2 : race g ≤ race gr + 1 := race_le_succ_race_of_mem_rightMoves hg hgr_mem
  exact ⟨gr, hgr_mem, by omega⟩

/--
If $G$ and $H$ are Left dead ends with $G \ge H$, then $T(G) \subseteq T(H)$.

This is [Davies (Theorem 3.17 on p. 16)][davies:FactorisationsLeftDead:2024].
-/
theorem terminalLengths_subset_of_ge {g h : GameForm} (hg : IsLde g) (hh : IsLde h)
    (hge : g ≥ₗ h) : terminalLengths g ⊆ terminalLengths h := by
  by_cases hg0 : g = 0
  · subst hg0
    have h_right_end : IsEnd .right h := ((misereGE_lde_iff isLde_zero hh).mp hge).1 isEnd_zero
    have hh0 : h = 0 := GameForm.both_ends_eq_zero (isEnd_of_isDeadEnd hh.deadEnd) h_right_end
    subst hh0
    exact Set.Subset.rfl
  · intro t ht
    rw [terminalLengths_of_ne_zero hg0] at ht
    simp only [Set.mem_iUnion, Set.mem_image] at ht
    obtain ⟨gr, hgr_mem, t', ht'_mem, ht'_eq⟩ := ht
    obtain ⟨hr, hhr_mem, hge_gr_hr⟩ := ((misereGE_lde_iff hg hh).mp hge).2 gr hgr_mem
    have hh_ne : h ≠ 0 := by
      rintro rfl
      exact absurd hhr_mem (by simp)
    have ht'_sub := terminalLengths_subset_of_ge (hg.of_mem_rightMoves hgr_mem)
      (hh.of_mem_rightMoves hhr_mem) hge_gr_hr ht'_mem
    rw [terminalLengths_of_ne_zero hh_ne]
    simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨hr, hhr_mem, t', ht'_sub, ht'_eq⟩
termination_by g
decreasing_by form_wf

/--
If $G$ is a combinatorial game and $(G_0, G_1, \ldots, G_k)$ is a run of $G$ such that
$G_k \cong 0$, then we say the run is *terminal*.

This is [Davies (Definition 3.11 on p. 14)][davies:FactorisationsLeftDead:2024].
-/
@[expose] def IsTerminalRun (l : List GameForm) : Prop := IsRun l ∧ l.getLast? = some 0

/--
$n \in T(G)$ if and only if there exists a terminal run of $G$ of length $n$.

This is [Davies (Definition 3.12 on p. 14)][davies:FactorisationsLeftDead:2024], recovered
as a theorem from the recursive definition of `terminalLengths`.
-/
theorem mem_terminalLengths_iff_exists_terminalRun {g : GameForm} (hg : IsLde g) {n : ℕ} :
    n ∈ terminalLengths g ↔ ∃ l : List GameForm, IsTerminalRun (g :: l) ∧ l.length = n := by
  constructor
  · intro hn
    by_cases hg0 : g = 0
    · subst hg0
      rw [terminalLengths_zero, Set.mem_singleton_iff] at hn
      exact ⟨[], ⟨trivial, rfl⟩, hn.symm⟩
    · rw [terminalLengths_of_ne_zero hg0] at hn
      simp only [Set.mem_iUnion, Set.mem_image] at hn
      obtain ⟨gr, hgr_mem, t, ht_mem, ht_eq⟩ := hn
      obtain ⟨l, ⟨hl_run, hl_last⟩, hl_len⟩ :=
        (mem_terminalLengths_iff_exists_terminalRun (hg.of_mem_rightMoves hgr_mem)).mp ht_mem
      refine ⟨gr :: l, ⟨⟨hgr_mem, hl_run⟩, ?_⟩, by simp [hl_len, ← ht_eq]⟩
      rwa [List.getLast?_cons_cons]
  · rintro ⟨l, ⟨hl_run, hl_last⟩, rfl⟩
    match l with
    | [] =>
      rw [List.getLast?_singleton, Option.some_inj] at hl_last
      subst hl_last
      rw [terminalLengths_zero]
      rfl
    | (b :: l') =>
      obtain ⟨hb_mem, hb_run⟩ := hl_run
      have hg0 : g ≠ 0 := by
        rintro rfl
        exact absurd hb_mem (by simp)
      rw [List.getLast?_cons_cons] at hl_last
      have hb_mem_T : l'.length ∈ terminalLengths b :=
        (mem_terminalLengths_iff_exists_terminalRun (hg.of_mem_rightMoves hb_mem)).mpr
          ⟨l', ⟨hb_run, hl_last⟩, rfl⟩
      rw [terminalLengths_of_ne_zero hg0]
      simp only [Set.mem_iUnion, Set.mem_image, List.length_cons]
      exact ⟨b, hb_mem, l'.length, hb_mem_T, rfl⟩
termination_by g
decreasing_by all_goals form_wf

private theorem forall₂_terminalLengths_of_forall₂_ge :
    ∀ {l m : List GameForm}, (∀ x ∈ l, IsLde x) → (∀ y ∈ m, IsLde y) →
      List.Forall₂ (fun a b => a ≥ₗ b) l m →
      List.Forall₂ (fun a b => terminalLengths a ⊆ terminalLengths b) l m := by
  intro l m hl hm hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | @cons a b l' m' hab _ ih =>
    refine List.Forall₂.cons ?_ (ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (fun y hy => hm y (List.mem_cons_of_mem _ hy)))
    exact terminalLengths_subset_of_ge (hl a List.mem_cons_self) (hm b List.mem_cons_self) hab

/--
If $G$ and $H$ are Left dead ends with $G \ge H$, and $k$ is an integer satisfying
$0 \le k \le \tilde{b}(G)$, then, for any run $(G_0, G_1, \ldots, G_k)$ of $G$ of length $k$, there
exists a run $(H_0, H_1, \ldots, H_k)$ of $H$ of length $k$ such that
$T(G_i) \subseteq T(H_i)$ for every $0 \le i \le k$.

This is [Davies (Corollary 3.19 on p. 17)][davies:FactorisationsLeftDead:2024].
-/
theorem exists_run_terminalLengths_subset {g h : GameForm} (hg : IsLde g) (hh : IsLde h)
    (hge : g ≥ₗ h) {l : List GameForm} (hl : IsRun (g :: l)) :
    ∃ m : List GameForm, IsRun (h :: m) ∧
      List.Forall₂ (fun a b => terminalLengths a ⊆ terminalLengths b) (g :: l) (h :: m) := by
  obtain ⟨m, hm_run, hm_rel⟩ := exists_run_dominated hg hh hge hl
  exact ⟨m, hm_run, forall₂_terminalLengths_of_forall₂_ge (hg.of_mem_isRun hl)
    (hh.of_mem_isRun hm_run) hm_rel⟩

/--
If $G$ and $H$ are Left dead ends with $G \ge H$, then $r(G) \ge r(H)$.

This is the race half of
[Davies (Corollary 3.18 on p. 16)][davies:FactorisationsLeftDead:2024].
-/
theorem race_ge_of_ge {g h : GameForm} (hg : IsLde g) (hh : IsLde h) (hge : g ≥ₗ h) :
    race h ≤ race g := by
  have h_mem : race g ∈ terminalLengths g := Nat.sInf_mem (terminalLengths_finite_nonempty hg).2
  exact Nat.sInf_le (terminalLengths_subset_of_ge hg hh hge h_mem)

/-- On a Left dead end, $b(G) = \max(T(G))$. -/
theorem birthday_eq_sSup_terminalLengths {g : GameForm} (hg : IsLde g) :
    birthday g = (sSup (terminalLengths g) : ℕ) := by
  by_cases hg0 : g = 0
  · subst hg0
    rw [terminalLengths_zero, birthday_zero]
    simp
  have h_fin := (terminalLengths_finite_nonempty hg).1
  have h_ne := (terminalLengths_finite_nonempty hg).2
  have h_mem : sSup (terminalLengths g) ∈ terminalLengths g := Nat.sSup_mem h_ne h_fin.bddAbove
  refine le_antisymm ?_ ?_
  · rw [birthday_le_iff]
    refine ⟨fun y hy => ?_, fun gr hgr => ?_⟩
    · have h_left : moves .left g = ∅ := by
        rw [← isEnd_def]
        exact isEnd_of_isDeadEnd hg.deadEnd
      rw [h_left] at hy
      simp at hy
    · have hgr_lde := hg.of_mem_rightMoves hgr
      have h_gr_mem : sSup (terminalLengths gr) ∈ terminalLengths gr :=
        Nat.sSup_mem (terminalLengths_finite_nonempty hgr_lde).2
          (terminalLengths_finite_nonempty hgr_lde).1.bddAbove
      have h_succ_le : sSup (terminalLengths gr) + 1 ≤ sSup (terminalLengths g) := by
        refine le_csSup h_fin.bddAbove ?_
        rw [terminalLengths_of_ne_zero hg0]
        simp only [Set.mem_iUnion, Set.mem_image]
        exact ⟨gr, hgr, sSup (terminalLengths gr), h_gr_mem, rfl⟩
      rw [birthday_eq_sSup_terminalLengths hgr_lde]
      exact_mod_cast Nat.lt_of_succ_le h_succ_le
  · have h_mem' : sSup (terminalLengths g) ∈
        ⋃ gr ∈ moves .right g, (· + 1) '' terminalLengths gr := by
      rw [← terminalLengths_of_ne_zero hg0]
      exact h_mem
    simp only [Set.mem_iUnion, Set.mem_image] at h_mem'
    obtain ⟨gr, hgr, t, ht, ht_eq⟩ := h_mem'
    have hgr_lde := hg.of_mem_rightMoves hgr
    have h_t_le : t ≤ sSup (terminalLengths gr) :=
      le_csSup (terminalLengths_finite_nonempty hgr_lde).1.bddAbove ht
    have h_bd : birthday gr < birthday g := birthday_lt_of_mem_moves hgr
    rw [birthday_eq_sSup_terminalLengths hgr_lde] at h_bd
    have h_le : sSup (terminalLengths g) ≤ sSup (terminalLengths gr) + 1 := by omega
    have h_cast : ((sSup (terminalLengths g) : ℕ) : NatOrdinal)
        ≤ ((sSup (terminalLengths gr) : ℕ) : NatOrdinal) + 1 := by exact_mod_cast h_le
    exact h_cast.trans (Order.add_one_le_of_lt h_bd)
termination_by g
decreasing_by form_wf

/--
If $G$ and $H$ are Left dead ends with $G \ge H$, then $b(G) \le b(H)$.

This is the birthday half of
[Davies (Corollary 3.18 on p. 16)][davies:FactorisationsLeftDead:2024].
-/
theorem birthday_le_of_ge {g h : GameForm} (hg : IsLde g) (hh : IsLde h) (hge : g ≥ₗ h) :
    birthday g ≤ birthday h := by
  rw [birthday_eq_sSup_terminalLengths hg, birthday_eq_sSup_terminalLengths hh]
  have h_le : sSup (terminalLengths g) ≤ sSup (terminalLengths h) :=
    csSup_le_csSup (terminalLengths_finite_nonempty hh).1.bddAbove
      (terminalLengths_finite_nonempty hg).2 (terminalLengths_subset_of_ge hg hh hge)
  exact_mod_cast h_le

theorem terminalLengths_eq_of_misereEQ {g h : GameForm} (hg : IsLde g) (hh : IsLde h)
    (heq : g ≡ₗ h) : terminalLengths g = terminalLengths h :=
  Set.Subset.antisymm (terminalLengths_subset_of_ge hg hh (misereGE_of_misereEQ heq))
    (terminalLengths_subset_of_ge hh hg (misereGE_of_misereEQ heq.symm))

theorem birthday_eq_of_misereEQ {g h : GameForm} (hg : IsLde g) (hh : IsLde h)
    (heq : g ≡ₗ h) : birthday g = birthday h := by
  rw [birthday_eq_sSup_terminalLengths hg, birthday_eq_sSup_terminalLengths hh,
    terminalLengths_eq_of_misereEQ hg hh heq]

theorem isInteger_iff_of_misereEQ {g h : GameForm} (hg : IsLde g) (hh : IsLde h)
    (heq : g ≡ₗ h) : IsInteger g ↔ IsInteger h := by
  rw [isInteger_iff_terminalLengths_subsingleton hg, isInteger_iff_terminalLengths_subsingleton hh,
    terminalLengths_eq_of_misereEQ hg hh heq]

theorem birthday_pos_of_ne_zero {g : GameForm} (hg : IsLde g) (hg0 : g ≠ 0) : 0 < birthday g := by
  rw [birthday_eq_sSup_terminalLengths hg]
  have h_mem : sSup (terminalLengths g) ∈ terminalLengths g :=
    Nat.sSup_mem (terminalLengths_finite_nonempty hg).2
      (terminalLengths_finite_nonempty hg).1.bddAbove
  have h_race : 1 ≤ race g :=
    Nat.one_le_iff_ne_zero.mpr fun hc => hg0 ((lde_race_zero_iff hg).mp hc)
  have h_one_le : 1 ≤ sSup (terminalLengths g) := le_trans h_race (Nat.sInf_le h_mem)
  exact_mod_cast h_one_le

/--
If $G$ is a Left dead end, then the following are equivalent: $G = 0$; $G \cong 0$;
$0 \in T(G)$; $r(G) = 0$; $b(G) = 0$.

This is [Davies (Lemma 3.16 on p. 15)][davies:FactorisationsLeftDead:2024].
-/
theorem lde_zero_tfae {g : GameForm} (hg : IsLde g) :
    List.TFAE [g ≡ₗ 0, g = 0, (0 : ℕ) ∈ terminalLengths g, race g = 0, birthday g = 0] := by
  tfae_have 1 ↔ 2 := lde_misereEQ_zero_iff hg
  tfae_have 2 → 3 := fun h => by rw [h, terminalLengths_zero]; rfl
  tfae_have 3 → 4 := fun h => Nat.le_zero.mp (Nat.sInf_le h)
  tfae_have 4 → 2 := fun h => (lde_race_zero_iff hg).mp h
  tfae_have 2 → 5 := fun h => by rw [h, birthday_zero]
  tfae_have 5 → 2 := fun h => by
    by_contra hne
    exact absurd h (birthday_pos_of_ne_zero hg hne).ne'
  tfae_finish

theorem race_eq_of_misereEQ {g h : GameForm} (hg : IsLde g) (hh : IsLde h) (heq : g ≡ₗ h) :
    race g = race h :=
  le_antisymm (race_ge_of_ge hh hg (misereGE_of_misereEQ heq.symm))
    (race_ge_of_ge hg hh (misereGE_of_misereEQ heq))

theorem exists_mem_rightMoves_birthday_succ {g : GameForm} (hg : IsLde g) (hg0 : g ≠ 0) :
    ∃ gr ∈ moves .right g, birthday g = birthday gr + 1 := by
  set M := sSup (terminalLengths g) with hM
  have h_mem : M ∈ terminalLengths g :=
    Nat.sSup_mem (terminalLengths_finite_nonempty hg).2 (terminalLengths_finite_nonempty hg).1.bddAbove
  rw [terminalLengths_of_ne_zero hg0] at h_mem
  simp only [Set.mem_iUnion, Set.mem_image] at h_mem
  obtain ⟨gr, hgr_mem, t, ht_mem, ht_eq⟩ := h_mem
  have hgr_lde := hg.of_mem_rightMoves hgr_mem
  refine ⟨gr, hgr_mem, ?_⟩
  have h1 : birthday gr < birthday g := birthday_lt_of_mem_moves hgr_mem
  have h_t_le : t ≤ sSup (terminalLengths gr) :=
    le_csSup (terminalLengths_finite_nonempty hgr_lde).1.bddAbove ht_mem
  have h_nat_le : M ≤ sSup (terminalLengths gr) + 1 := by omega
  have h2 : birthday g ≤ birthday gr + 1 := by
    rw [birthday_eq_sSup_terminalLengths hg, ← hM, birthday_eq_sSup_terminalLengths hgr_lde]
    exact_mod_cast h_nat_le
  exact le_antisymm h2 (Order.add_one_le_of_lt h1)

/--
If $G$ and $H$ are Left dead ends, then $T(G + H) = T(G) + T(H)$, a Minkowski sum.

This is [Davies (Proposition 3.20 on p. 18)][davies:FactorisationsLeftDead:2024].
-/
theorem terminalLengths_add {g h : GameForm} (hg : IsLde g) (hh : IsLde h) :
    terminalLengths (g + h) = { a + b | (a ∈ terminalLengths g) (b ∈ terminalLengths h) } := by
  by_cases hg0 : g = 0
  · subst hg0
    rw [zero_add, terminalLengths_zero]
    ext n
    constructor
    · intro hn
      exact ⟨0, rfl, n, hn, by omega⟩
    · rintro ⟨a, rfl, b, hb, rfl⟩
      simpa using hb
  · by_cases hh0 : h = 0
    · subst hh0
      rw [add_zero, terminalLengths_zero]
      ext n
      constructor
      · intro hn
        exact ⟨n, hn, 0, rfl, by omega⟩
      · rintro ⟨a, ha, b, rfl, rfl⟩
        simpa using ha
    · have hgh_ne : g + h ≠ 0 := by
        intro hc
        obtain ⟨gr, hgr_mem⟩ := hg.rightMoves_nonempty hg0
        have h_mem : gr + h ∈ moves .right (g + h) := by
          rw [moves_add]; exact Or.inl ⟨gr, hgr_mem, rfl⟩
        rw [hc] at h_mem
        simp at h_mem
      rw [terminalLengths_of_ne_zero hgh_ne, moves_add]
      ext n
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_union]
      constructor
      · rintro ⟨x, (⟨gr, hgr_mem, rfl⟩ | ⟨hr, hhr_mem, rfl⟩), t, ht_mem, rfl⟩
        · have hIH := terminalLengths_add (hg.of_mem_rightMoves hgr_mem) hh
          rw [hIH] at ht_mem
          obtain ⟨a, ha, b, hb, hab⟩ := ht_mem
          refine ⟨a + 1, ?_, b, hb, by omega⟩
          rw [terminalLengths_of_ne_zero hg0]
          simp only [Set.mem_iUnion, Set.mem_image]
          exact ⟨gr, hgr_mem, a, ha, rfl⟩
        · have hIH := terminalLengths_add hg (hh.of_mem_rightMoves hhr_mem)
          rw [hIH] at ht_mem
          obtain ⟨a, ha, b, hb, hab⟩ := ht_mem
          refine ⟨a, ha, b + 1, ?_, by omega⟩
          rw [terminalLengths_of_ne_zero hh0]
          simp only [Set.mem_iUnion, Set.mem_image]
          exact ⟨hr, hhr_mem, b, hb, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        rw [terminalLengths_of_ne_zero hg0] at ha
        simp only [Set.mem_iUnion, Set.mem_image] at ha
        obtain ⟨gr, hgr_mem, a', ha'_mem, ha'_eq⟩ := ha
        have hIH := terminalLengths_add (hg.of_mem_rightMoves hgr_mem) hh
        refine ⟨gr + h, Or.inl ⟨gr, hgr_mem, rfl⟩, a' + b, ?_, by omega⟩
        rw [hIH]
        exact ⟨a', ha'_mem, b, hb, rfl⟩
termination_by (g, h)
decreasing_by all_goals form_wf

theorem not_isInteger_add_of_not_isInteger_right {h k : GameForm} (hh : IsLde h) (hk : IsLde k)
    (hk_ni : ¬ IsInteger k) : ¬ IsInteger (h + k) := by
  intro hc
  have h_sub : (terminalLengths (h + k)).Subsingleton :=
    (isInteger_iff_terminalLengths_subsingleton (hh.add hk)).mp hc
  obtain ⟨t0, ht0⟩ := (terminalLengths_finite_nonempty hh).2
  have hk_sub : (terminalLengths k).Subsingleton := by
    intro a ha b hb
    have hxa : t0 + a ∈ terminalLengths (h + k) := by
      rw [terminalLengths_add hh hk]; exact ⟨t0, ht0, a, ha, rfl⟩
    have hxb : t0 + b ∈ terminalLengths (h + k) := by
      rw [terminalLengths_add hh hk]; exact ⟨t0, ht0, b, hb, rfl⟩
    have := h_sub hxa hxb
    omega
  exact hk_ni ((isInteger_iff_terminalLengths_subsingleton hk).mpr hk_sub)

theorem isInteger_add_neg_intCast_iff {h : GameForm} (hh : IsLde h) (n : ℕ) :
    IsInteger (h + -(n : GameForm)) ↔ IsInteger h := by
  have h_shift : terminalLengths (h + -(n : GameForm)) = (· + n) '' terminalLengths h := by
    rw [terminalLengths_add hh (isLde_neg_intCast n), terminalLengths_neg_intCast]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, b, rfl, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, n, rfl, rfl⟩
  rw [isInteger_iff_terminalLengths_subsingleton (hh.add (isLde_neg_intCast n)),
    isInteger_iff_terminalLengths_subsingleton hh, h_shift]
  constructor
  · intro hsub a ha b hb
    exact add_right_cancel (hsub ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
  · intro hsub x hx y hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [hsub ha hb]

theorem birthday_lt_flexibility_add_of_not_isInteger {h k : GameForm} (hh : IsLde h)
    (hk : IsLde k) (hh0 : h ≠ 0) (hk_ni : ¬ IsInteger k) :
    birthday h < (flexibility (h + k) : NatOrdinal) := by
  obtain ⟨hr, hhr_mem, hb_eq⟩ := exists_mem_rightMoves_birthday_succ hh hh0
  have hhr_lde := hh.of_mem_rightMoves hhr_mem
  have hnotint : ¬ IsInteger (h + k) := not_isInteger_add_of_not_isInteger_right hh hk hk_ni
  have h_mem_opt : hr + k ∈ moves .right (h + k) := by
    rw [moves_add]; exact Or.inl ⟨hr, hhr_mem, rfl⟩
  have h_fin : ((fun x => flexibility x) '' moves .right (h + k)).Finite :=
    (IsShort.finite_moves .right (hh.add hk).short).image _
  have h_le : flexibility (hr + k) ≤ sSup ((fun x => flexibility x) '' moves .right (h + k)) :=
    le_csSup h_fin.bddAbove (Set.mem_image_of_mem _ h_mem_opt)
  have h_lt : birthday hr < flexibility (hr + k) := by
    by_cases hhr0 : hr = 0
    · subst hhr0
      rw [zero_add, birthday_zero]
      have : 1 ≤ flexibility k := by rw [flexibility_of_not_isInteger hk_ni]; omega
      exact_mod_cast this
    · exact birthday_lt_flexibility_add_of_not_isInteger hhr_lde hk hhr0 hk_ni
  set X := sSup ((fun x => flexibility x) '' moves .right (h + k)) with hX
  have h_le' : (flexibility (hr + k) : NatOrdinal) ≤ (X : NatOrdinal) := Nat.cast_le.mpr h_le
  have h_final : birthday hr < (X : NatOrdinal) := lt_of_lt_of_le h_lt h_le'
  have h_flex_eq : (flexibility (h + k) : NatOrdinal) = 1 + (X : NatOrdinal) := by
    rw [hX]; exact_mod_cast flexibility_of_not_isInteger hnotint
  rw [hb_eq, h_flex_eq]
  calc birthday hr + 1 ≤ (X : NatOrdinal) := Order.add_one_le_of_lt h_final
    _ < 1 + (X : NatOrdinal) := lt_add_of_pos_left _ zero_lt_one
termination_by h
decreasing_by form_wf

/--
If $G$ and $H$ are Left dead ends, then $r(G + H) = r(G) + r(H)$.

This is the race half of
[Davies (Proposition 3.20 on p. 18)][davies:FactorisationsLeftDead:2024].
-/
theorem race_add {g h : GameForm} (hg : IsLde g) (hh : IsLde h) :
    race (g + h) = race g + race h := by
  apply le_antisymm
  · have h_mem : race g + race h ∈ terminalLengths (g + h) := by
      rw [terminalLengths_add hg hh]
      exact ⟨race g, Nat.sInf_mem (terminalLengths_finite_nonempty hg).2,
        race h, Nat.sInf_mem (terminalLengths_finite_nonempty hh).2, rfl⟩
    exact Nat.sInf_le h_mem
  · have h_mem : race (g + h) ∈ terminalLengths (g + h) :=
      Nat.sInf_mem (terminalLengths_finite_nonempty (hg.add hh)).2
    rw [terminalLengths_add hg hh] at h_mem
    obtain ⟨a, ha, b, hb, hab⟩ := h_mem
    calc race g + race h ≤ a + b := Nat.add_le_add (Nat.sInf_le ha) (Nat.sInf_le hb)
      _ = race (g + h) := hab

theorem race_lt_sSup_terminalLengths {g : GameForm} (hg : IsLde g) (hgi : ¬ IsInteger g) :
    race g < sSup (terminalLengths g) := by
  have hT := terminalLengths_finite_nonempty hg
  by_contra hc
  push_neg at hc
  refine hgi ((isInteger_iff_terminalLengths_subsingleton hg).mpr fun a ha b hb => ?_)
  have ha1 : race g ≤ a := Nat.sInf_le ha
  have ha2 : a ≤ sSup (terminalLengths g) := le_csSup hT.1.bddAbove ha
  have hb1 : race g ≤ b := Nat.sInf_le hb
  have hb2 : b ≤ sSup (terminalLengths g) := le_csSup hT.1.bddAbove hb
  omega

/--
If $G$ and $H$ are Left dead ends, then $|T(G + H)| \ge \max(|T(G)|, |T(H)|)$.

This is the inequality half of
[Davies (Corollary 3.21 on p. 18)][davies:FactorisationsLeftDead:2024].
-/
theorem ncard_terminalLengths_add_ge {g h : GameForm} (hg : IsLde g) (hh : IsLde h) :
    max (terminalLengths g).ncard (terminalLengths h).ncard
      ≤ (terminalLengths (g + h)).ncard := by
  have h_fin := (terminalLengths_finite_nonempty (hg.add hh)).1
  have hg_mem : race g ∈ terminalLengths g := Nat.sInf_mem (terminalLengths_finite_nonempty hg).2
  have hh_mem : race h ∈ terminalLengths h := Nat.sInf_mem (terminalLengths_finite_nonempty hh).2
  refine max_le ?_ ?_
  · refine Set.ncard_le_ncard_of_injOn (· + race h) (fun a ha => ?_)
      (fun a _ b _ hab => by simpa using hab) h_fin
    rw [terminalLengths_add hg hh]
    exact ⟨a, ha, race h, hh_mem, rfl⟩
  · refine Set.ncard_le_ncard_of_injOn (race g + ·) (fun b hb => ?_)
      (fun a _ b _ hab => by simpa using hab) h_fin
    rw [terminalLengths_add hg hh]
    exact ⟨race g, hg_mem, b, hb, rfl⟩

private theorem ncard_lt_ncard_terminalLengths_add {g h : GameForm} (hg : IsLde g) (hh : IsLde h)
    (hgi : ¬ IsInteger g) :
    (terminalLengths h).ncard < (terminalLengths (g + h)).ncard := by
  have hTg := terminalLengths_finite_nonempty hg
  have hTh := terminalLengths_finite_nonempty hh
  have h_fin := (terminalLengths_finite_nonempty (hg.add hh)).1
  have hg_min : race g ∈ terminalLengths g := Nat.sInf_mem hTg.2
  have hg_max : sSup (terminalLengths g) ∈ terminalLengths g := Nat.sSup_mem hTg.2 hTg.1.bddAbove
  have hh_max : sSup (terminalLengths h) ∈ terminalLengths h := Nat.sSup_mem hTh.2 hTh.1.bddAbove
  have h_lt : race g < sSup (terminalLengths g) := race_lt_sSup_terminalLengths hg hgi
  set b := sSup (terminalLengths h) with hb
  set S : Set ℕ := insert (sSup (terminalLengths g) + b) ((race g + ·) '' terminalLengths h) with hS
  have h_notmem : sSup (terminalLengths g) + b ∉ (race g + ·) '' terminalLengths h := by
    rintro ⟨t, ht, heq⟩
    simp only at heq
    have h_t_le : t ≤ b := le_csSup hTh.1.bddAbove ht
    omega
  have h_sub : S ⊆ terminalLengths (g + h) := by
    rw [hS, terminalLengths_add hg hh]
    rintro x (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨_, hg_max, b, hh_max, rfl⟩
    · exact ⟨race g, hg_min, t, ht, rfl⟩
  have h_card : S.ncard = (terminalLengths h).ncard + 1 := by
    rw [hS, Set.ncard_insert_of_notMem h_notmem (hTh.1.image _),
      Set.ncard_image_of_injective _ (fun a c hac => by omega)]
  have h_le : S.ncard ≤ (terminalLengths (g + h)).ncard := Set.ncard_le_ncard h_sub h_fin
  omega

private theorem ncard_terminalLengths_add_of_isInteger {g h : GameForm} (hg : IsLde g)
    (hh : IsLde h) (hgi : IsInteger g) :
    (terminalLengths (g + h)).ncard = (terminalLengths h).ncard := by
  obtain ⟨n, rfl⟩ := exists_eq_neg_intCast_of_isInteger hg hgi
  have h_eq : terminalLengths (-(n : GameForm) + h) = (n + ·) '' terminalLengths h := by
    rw [terminalLengths_add hg hh, terminalLengths_neg_intCast]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, rfl, c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨n, rfl, c, hc, rfl⟩
  rw [h_eq, Set.ncard_image_of_injective _ (fun a c hac => by omega)]

/--
If $G$ and $H$ are Left dead ends, then $|T(G + H)| \ge \max(|T(G)|, |T(H)|)$, with
equality if and only if at least one of $G$ and $H$ is an integer.

This is [Davies (Corollary 3.21 on p. 18)][davies:FactorisationsLeftDead:2024].
-/
theorem ncard_terminalLengths_add_eq_max_iff {g h : GameForm} (hg : IsLde g) (hh : IsLde h) :
    (terminalLengths (g + h)).ncard = max (terminalLengths g).ncard (terminalLengths h).ncard
      ↔ (IsInteger g ∨ IsInteger h) := by
  have hTg := terminalLengths_finite_nonempty hg
  have hTh := terminalLengths_finite_nonempty hh
  have hg_pos : 0 < (terminalLengths g).ncard := (Set.ncard_pos hTg.1).mpr hTg.2
  have hh_pos : 0 < (terminalLengths h).ncard := (Set.ncard_pos hTh.1).mpr hTh.2
  constructor
  · intro h_eq
    by_contra hc
    push_neg at hc
    have h1 := ncard_lt_ncard_terminalLengths_add hg hh hc.1
    have h2 : (terminalLengths g).ncard < (terminalLengths (g + h)).ncard := by
      rw [add_comm]
      exact ncard_lt_ncard_terminalLengths_add hh hg hc.2
    omega
  · rintro (hgi | hhi)
    · obtain ⟨n, hn⟩ := exists_eq_neg_intCast_of_isInteger hg hgi
      have h_one : (terminalLengths g).ncard = 1 := by
        rw [hn, terminalLengths_neg_intCast, Set.ncard_singleton]
      rw [ncard_terminalLengths_add_of_isInteger hg hh hgi, h_one]
      omega
    · obtain ⟨n, hn⟩ := exists_eq_neg_intCast_of_isInteger hh hhi
      have h_one : (terminalLengths h).ncard = 1 := by
        rw [hn, terminalLengths_neg_intCast, Set.ncard_singleton]
      have h_swap : (terminalLengths (g + h)).ncard = (terminalLengths g).ncard := by
        rw [add_comm]
        exact ncard_terminalLengths_add_of_isInteger hh hg hhi
      rw [h_swap, h_one]
      omega

/-! ## Pocancellativity and cancellativity -/

@[expose] def IsPocancellativeIn (A : GameForm → Prop) (j : GameForm) : Prop :=
  ∀ g h, A g → A h → MisereGE A (g + j) (h + j) → MisereGE A g h

@[expose] def IsCancellativeIn (A : GameForm → Prop) (j : GameForm) : Prop :=
  ∀ g h, A g → A h → MisereEQ A (g + j) (h + j) → MisereEQ A g h

/--
If $\mathcal{U}$ is a universe, $G, H \in \mathcal{U}$ are Left dead ends, and $J$ is a
pocancellative element of $\mathcal{U}$ satisfying $G + J \ge H + J$, then $G \ge H$.

This is [Davies (Lemma 3.5 on p. 12)][davies:FactorisationsLeftDead:2024].
-/
theorem lde_ge_of_add_pocancellative {A : GameForm → Prop} {g h j : GameForm}
    (hgA : A g) (hhA : A h) (hj : IsPocancellativeIn A j)
    (hge : MisereGE A (g + j) (h + j)) : MisereGE A g h :=
  hj g h hgA hhA hge

/--
If $\mathcal{U}$ is a universe, $G, H \in \mathcal{U}$ are Left dead ends, and $J$ is a
cancellative element of $\mathcal{U}$ satisfying $G + J = H + J$, then $G = H$.

This is [Davies (Lemma 3.6 on p. 12)][davies:FactorisationsLeftDead:2024].
-/
theorem lde_misereEQ_of_add_cancellative {A : GameForm → Prop} {g h j : GameForm}
    (hgA : A g) (hhA : A h) (hj : IsCancellativeIn A j)
    (heq : MisereEQ A (g + j) (h + j)) : MisereEQ A g h :=
  hj g h hgA hhA heq

theorem isPocancellativeIn_of_add_neg {A : GameForm → Prop} [ClosedUnderAdd A]
    [ClosedUnderNeg A] {j : GameForm} (hj : A j) (hinv : MisereEQ A (j + -j) 0) :
    IsPocancellativeIn A j := by
  intro g h hgA hhA hge
  have hnj : A (-j) := ClosedUnderNeg.neg_of hj
  have hjnj : A (j + -j) := ClosedUnderAdd.has_add _ _ hj hnj
  have h1 : MisereGE A (g + j + -j) (h + j + -j) :=
    Form.MisereQuotient.add_misereGE_add_right hnj hge
  have collapse : ∀ x, A x → MisereEQ A (x + j + -j) x := by
    intro x hx
    rw [add_assoc]
    have := Form.MisereQuotient.add_misereEQ_add (A := A) hjnj hx
      (fun _ _ => rfl : MisereEQ A x x) hinv
    rwa [add_zero] at this
  exact ((misereGE_of_misereEQ (collapse g hgA).symm).trans h1).trans
    (misereGE_of_misereEQ (collapse h hhA))

theorem isCancellativeIn_of_add_neg {A : GameForm → Prop} [ClosedUnderAdd A]
    [ClosedUnderNeg A] {j : GameForm} (hj : A j) (hinv : MisereEQ A (j + -j) 0) :
    IsCancellativeIn A j := fun g h hgA hhA heq =>
  MisereEq.of_antisymm
    (isPocancellativeIn_of_add_neg hj hinv g h hgA hhA (misereGE_of_misereEQ heq))
    (isPocancellativeIn_of_add_neg hj hinv h g hhA hgA (misereGE_of_misereEQ heq.symm))

/--
If $G$ is a dead Right end and $H$ is a dead Left end, then $o^-(G + H)$ is $\mathcal{N}^-$
when $l(G) = r(H)$, $\mathcal{L}^-$ when $l(G) < r(H)$, and $\mathcal{R}^-$ when
$l(G) > r(H)$.

This is [Milley, Renault (Lemma 5 on p. 7)][milley:DeadEndsMisere:2013].
-/
theorem winsGoingFirst_left_neg_add :
    ∀ (a b : GameForm), IsLde a → IsLde b →
      (race a ≤ race b → WinsGoingFirst .left ((-a) + b)) ∧
      (race a < race b → ¬ WinsGoingFirst .right ((-a) + b)) := by
  intro a b ha hb
  have hbl : moves .left b = ∅ := by
    rw [← isEnd_def]
    exact isEnd_of_isDeadEnd hb.deadEnd
  have hal : moves .left a = ∅ := by
    rw [← isEnd_def]
    exact isEnd_of_isDeadEnd ha.deadEnd
  -- `-a` is a Right end: Right can never move in the Right-dead-end component.
  have har_neg : moves .right (-a) = (∅ : Set GameForm) := by
    rw [moves_neg, Player.neg_right, hal]
    simp
  constructor
  · intro hle
    by_cases ha0 : a = 0
    · refine winsGoingFirst_of_isEnd ?_
      rw [isEnd_def, moves_add, moves_neg, ha0]
      simp [hbl]
    · obtain ⟨ar, har_mem, har_race⟩ := exists_mem_rightMoves_race_succ ha ha0
      refine winsGoingFirst_of_moves ⟨(-ar) + b, ?_, ?_⟩
      · rw [moves_add]
        refine Or.inl ⟨-ar, ?_, rfl⟩
        simp only [moves_neg, Player.neg_left, Set.mem_neg, neg_neg]
        exact har_mem
      · rw [Player.neg_left]
        exact (winsGoingFirst_left_neg_add ar b (ha.of_mem_rightMoves har_mem) hb).2 (by omega)
  · intro hlt
    have hb0 : b ≠ 0 := by
      intro hc
      rw [(lde_race_zero_iff hb).mpr hc] at hlt
      omega
    rw [not_winsGoingFirst_iff]
    refine ⟨?_, fun g' hg' => ?_⟩
    · rw [GameForm.isEndLike_iff_isEnd, isEnd_def]
      intro hend
      obtain ⟨br, hbr_mem⟩ := hb.rightMoves_nonempty hb0
      have hmem : (-a) + br ∈ moves .right ((-a) + b) := by
        rw [moves_add]
        exact Or.inr ⟨br, hbr_mem, rfl⟩
      rw [hend] at hmem
      exact Set.notMem_empty _ hmem
    · rw [Player.neg_right]
      rw [moves_add, har_neg] at hg'
      simp only [Set.image_empty, Set.empty_union, Set.mem_image] at hg'
      obtain ⟨br, hbr_mem, rfl⟩ := hg'
      have h_le : race b ≤ race br + 1 := race_le_succ_race_of_mem_rightMoves hb hbr_mem
      exact (winsGoingFirst_left_neg_add a br ha (hb.of_mem_rightMoves hbr_mem)).1 (by omega)
termination_by a b => (a, b)
decreasing_by all_goals form_wf

private theorem strong_left_add_neg {k : GameForm} (hk : IsLde k) :
    Strong Form.DeadEnding.ShortDeadEnding (k + -k) .left := by
  intro x hx hxe
  have hxe' : IsEnd .left x := GameForm.isEndLike_iff_isEnd.mp hxe
  have hx_lde : IsLde x := ⟨hx.short, isDeadEnd_of_isDeadEnding hx.dead_ending hxe'⟩
  have h_eq : k + -k + x = (-k) + (k + x) := by
    rw [add_assoc, add_left_comm]
  rw [h_eq]
  refine (winsGoingFirst_left_neg_add k (k + x) hk (hk.add hx_lde)).1 ?_
  rw [race_add hk hx_lde]
  omega

private theorem strong_right_add_neg {k : GameForm} (hk : IsLde k) :
    Strong Form.DeadEnding.ShortDeadEnding (k + -k) .right := by
  intro x hx hxe
  have hxe' : IsEnd .right x := GameForm.isEndLike_iff_isEnd.mp hxe
  have hnx : Form.DeadEnding.ShortDeadEnding (-x) := ClosedUnderNeg.neg_of hx
  have hnxe : IsEndLike .left (-x) :=
    GameForm.isEndLike_iff_isEnd.mpr (IsEnd.neg_iff_neg.mpr hxe')
  have h_neg : WinsGoingFirst .right (k + -k + x) ↔ WinsGoingFirst .left (-(k + -k + x)) := by
    rw [winsGoingFirst_neg_iff, Player.neg_left]
  rw [h_neg]
  have h_eq : -(k + -k + x) = k + -k + (-x) := by
    rw [neg_add, neg_add, neg_neg, add_comm (-k) k]
  rw [h_eq]
  exact strong_left_add_neg hk (-x) hnx hnxe

/--
If $G$ is a dead end then $G + \overline{G} \equiv 0 \pmod{\mathcal{E}}$.

This is [Milley, Renault (Theorem 6 on p. 8)][milley:DeadEndsMisere:2013].
-/
theorem lde_add_neg_misereEQ {k : GameForm} (hk : IsLde k) : (k + -k) ≡ₗ 0 := by
  by_cases hk0 : k = 0
  · subst hk0
    intro x _
    simp
  have hkl : moves .left k = ∅ := by
    rw [← isEnd_def]
    exact isEnd_of_isDeadEnd hk.deadEnd
  have hknr : moves .right (-k) = (∅ : Set GameForm) := by
    rw [moves_neg, Player.neg_right, hkl]
    simp
  have hkr_ne : (moves .right k).Nonempty := hk.rightMoves_nonempty hk0
  refine MisereEq.of_antisymm ?_ ?_
  · refine Hereditary.misereGE_of_maintenance_proviso Form.DeadEnding.ShortDeadEnding
      ?_ ?_ ?_ ?_
    · intro gr hgr
      rw [moves_add, hknr] at hgr
      simp only [Set.image_empty, Set.union_empty, Set.mem_image] at hgr
      obtain ⟨kr, hkr_mem, rfl⟩ := hgr
      refine Or.inr ⟨kr + -kr, ?_, ?_⟩
      · rw [moves_add]
        refine Or.inr ⟨-kr, ?_, rfl⟩
        simp only [moves_neg, Player.neg_left, Set.mem_neg, neg_neg]
        exact hkr_mem
      · exact misereGE_of_misereEQ (lde_add_neg_misereEQ (hk.of_mem_rightMoves hkr_mem))
    · intro hl hhl
      simp only [moves_zero, Set.mem_empty_iff_false] at hhl
    · intro hend
      exfalso
      rw [GameForm.isEndLike_iff_isEnd, isEnd_def] at hend
      obtain ⟨kr, hkr_mem⟩ := hkr_ne
      have hmem : kr + -k ∈ moves .right (k + -k) := by
        rw [moves_add]
        exact Or.inl ⟨kr, hkr_mem, rfl⟩
      rw [hend] at hmem
      exact Set.notMem_empty _ hmem
    · intro _
      exact strong_left_add_neg hk
  · refine Hereditary.misereGE_of_maintenance_proviso Form.DeadEnding.ShortDeadEnding
      ?_ ?_ ?_ ?_
    · intro gr hgr
      simp only [moves_zero, Set.mem_empty_iff_false] at hgr
    · intro hl hhl
      rw [moves_add, hkl] at hhl
      simp only [Set.image_empty, Set.empty_union, Set.mem_image] at hhl
      obtain ⟨y, hy_mem, rfl⟩ := hhl
      have hny : -y ∈ moves .right k := by
        simpa only [moves_neg, Player.neg_left, Set.mem_neg] using hy_mem
      refine Or.inr ⟨-y + y, ?_, ?_⟩
      · rw [moves_add]
        exact Or.inl ⟨-y, hny, rfl⟩
      · have hIH := lde_add_neg_misereEQ (hk.of_mem_rightMoves hny)
        rw [neg_neg] at hIH
        exact misereGE_of_misereEQ hIH.symm
    · intro _
      exact strong_right_add_neg hk
    · intro hend
      exfalso
      rw [GameForm.isEndLike_iff_isEnd, isEnd_def] at hend
      obtain ⟨kr, hkr_mem⟩ := hkr_ne
      have hmem : k + -kr ∈ moves .left (k + -k) := by
        rw [moves_add]
        refine Or.inr ⟨-kr, ?_, rfl⟩
        simp only [moves_neg, Player.neg_left, Set.mem_neg, neg_neg]
        exact hkr_mem
      rw [hend] at hmem
      exact Set.notMem_empty _ hmem
termination_by k
decreasing_by all_goals form_wf

theorem isPocancellativeIn_of_isLde {k : GameForm} (hk : IsLde k) :
    IsPocancellativeIn Form.DeadEnding.ShortDeadEnding k :=
  isPocancellativeIn_of_add_neg hk.shortDeadEnding (lde_add_neg_misereEQ hk)

/--
The monoid of Left dead ends $\mathcal{L}$ is pocancellative.

This is [Davies (Theorem 3.7 on p. 12)][davies:FactorisationsLeftDead:2024].
-/
theorem lde_pocancellative {g h k : GameForm} (hg : IsLde g) (hh : IsLde h) (hk : IsLde k)
    (hge : (g + k) ≥ₗ (h + k)) : g ≥ₗ h :=
  lde_ge_of_add_pocancellative hg.shortDeadEnding hh.shortDeadEnding
    (isPocancellativeIn_of_isLde hk) hge

/--
The monoid of Left dead ends $\mathcal{L}$ is cancellative.

This is [Davies (Theorem 3.7 on p. 12)][davies:FactorisationsLeftDead:2024].
-/
theorem lde_cancellative {g h k : GameForm} (hg : IsLde g) (hh : IsLde h) (hk : IsLde k)
    (heq : (g + k) ≡ₗ (h + k)) : g ≡ₗ h :=
  lde_misereEQ_of_add_cancellative hg.shortDeadEnding hh.shortDeadEnding
    (isCancellativeIn_of_add_neg hk.shortDeadEnding (lde_add_neg_misereEQ hk)) heq

theorem isLde_nsmul {g : GameForm} (hg : IsLde g) : ∀ n : ℕ, IsLde (n • g)
  | 0 => by rw [zero_nsmul]; exact isLde_zero
  | n + 1 => by rw [succ_nsmul]; exact (isLde_nsmul hg n).add hg

theorem add_nsmul_mem_rightMoves {g gr : GameForm} (hgr : gr ∈ moves .right g) (n : ℕ) :
    gr + n • g ∈ moves .right ((n + 1) • g) := by
  rw [succ_nsmul', moves_add]
  exact Or.inl ⟨gr, hgr, rfl⟩

theorem exists_eq_add_nsmul_of_mem_rightMoves {g : GameForm} (n : ℕ) {x : GameForm}
    (hx : x ∈ moves .right ((n + 1) • g)) : ∃ gr ∈ moves .right g, x = gr + n • g := by
  induction n generalizing x with
  | zero =>
    rw [zero_add, one_nsmul] at hx
    exact ⟨x, hx, by rw [zero_nsmul, add_zero]⟩
  | succ n ih =>
    rw [succ_nsmul', moves_add] at hx
    simp only [Set.mem_union, Set.mem_image] at hx
    rcases hx with ⟨gr, hgr, rfl⟩ | ⟨y, hy, rfl⟩
    · exact ⟨gr, hgr, rfl⟩
    · obtain ⟨gr, hgr, rfl⟩ := ih hy
      exact ⟨gr, hgr, by rw [succ_nsmul']; ac_rfl⟩

theorem nsmul_misereEQ_nsmul {a b : GameForm} (ha : IsLde a) (hb : IsLde b) (hab : a ≡ₗ b) :
    ∀ n : ℕ, (n • a) ≡ₗ (n • b)
  | 0 => by rw [zero_nsmul, zero_nsmul]; exact fun _ _ => rfl
  | n + 1 => by
    rw [succ_nsmul, succ_nsmul]
    exact Form.MisereQuotient.add_misereEQ_add ha.shortDeadEnding
      (isLde_nsmul hb n).shortDeadEnding (nsmul_misereEQ_nsmul ha hb hab n) hab

private theorem lde_nsmul_cancel_step {n : ℕ} (hn : 0 < n)
    (ihn : ∀ m, m < n → 0 < m → ∀ a b : GameForm.{u}, IsLde a → IsLde b →
      ((m • a) ≡ₗ (m • b)) → a ≡ₗ b)
    (g h : GameForm.{u}) (hg : IsLde g) (hh : IsLde h) (heq : (n • g) ≡ₗ (n • h)) : g ≡ₗ h := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa only [zero_add, one_nsmul] using heq
  by_cases hg0 : g = 0
  · subst hg0
    have h0 : ((m + 1) • h) = 0 := by
      refine (lde_misereEQ_zero_iff (isLde_nsmul hh _)).mp ?_
      rw [nsmul_zero] at heq
      exact heq.symm
    have hh0 : h = 0 := by
      by_contra hc
      obtain ⟨hr, hhr⟩ := hh.rightMoves_nonempty hc
      have hmem := add_nsmul_mem_rightMoves hhr m
      rw [h0, moves_zero] at hmem
      exact Set.notMem_empty _ hmem
    rw [hh0]
    exact fun _ _ => rfl
  have hng : IsLde ((m + 1) • g) := isLde_nsmul hg _
  have hnh : IsLde ((m + 1) • h) := isLde_nsmul hh _
  -- A good option of `(m+1) • g`, matched against one of `(m+1) • h` in both directions.
  obtain ⟨gr₀, hgr₀⟩ := hg.rightMoves_nonempty hg0
  obtain ⟨x, hx_good, -⟩ :=
    exists_isGoodOption_le_of_mem_rightMoves hng (add_nsmul_mem_rightMoves hgr₀ m)
  obtain ⟨y, hy_good, hxy⟩ :=
    lde_good_option_dominates hng hnh (misereGE_of_misereEQ heq) hx_good
  obtain ⟨z, hz_good, hyz⟩ :=
    lde_good_option_dominates hnh hng (misereGE_of_misereEQ heq.symm) hy_good
  have hzx : z ≥ₗ x := by
    by_contra hc
    exact hx_good.2 ⟨z, hz_good.1, hxy.trans hyz, hc⟩
  have hxy_eq : x ≡ₗ y := MisereEq.of_antisymm hxy (hyz.trans hzx)
  obtain ⟨G', hG', rfl⟩ := exists_eq_add_nsmul_of_mem_rightMoves m hx_good.1
  obtain ⟨H', hH', rfl⟩ := exists_eq_add_nsmul_of_mem_rightMoves m hy_good.1
  have hG'lde : IsLde G' := hg.of_mem_rightMoves hG'
  have hH'lde : IsLde H' := hh.of_mem_rightMoves hH'
  -- Multiply `G' + m • g ≡ H' + m • h` by `m + 1` and cancel the composite `(m+1)m` term.
  have hmul := nsmul_misereEQ_nsmul (hG'lde.add (isLde_nsmul hg m))
    (hH'lde.add (isLde_nsmul hh m)) hxy_eq (m + 1)
  rw [nsmul_add, nsmul_add, ← mul_nsmul, ← mul_nsmul] at hmul
  have hbig : ((m * (m + 1)) • g) ≡ₗ ((m * (m + 1)) • h) := by
    rw [mul_nsmul', mul_nsmul']
    exact nsmul_misereEQ_nsmul hng hnh heq m
  have hcancel : ((m + 1) • G' + (m * (m + 1)) • g) ≡ₗ ((m + 1) • H' + (m * (m + 1)) • g) :=
    hmul.trans (Form.MisereQuotient.add_misereEQ_add
      (isLde_nsmul hh _).shortDeadEnding (isLde_nsmul hH'lde _).shortDeadEnding
      (fun _ _ => rfl) hbig.symm)
  have hG'eq : ((m + 1) • G') ≡ₗ ((m + 1) • H') :=
    lde_cancellative (isLde_nsmul hG'lde _) (isLde_nsmul hH'lde _) (isLde_nsmul hg _) hcancel
  have hGH : G' ≡ₗ H' := lde_nsmul_cancel_step hn ihn G' H' hG'lde hH'lde hG'eq
  -- Cancelling `G' ≡ H'` from the matched options leaves `m • g ≡ m • h`.
  have hstep : ((m • g) + G') ≡ₗ ((m • h) + G') := by
    rw [add_comm (m • g) G', add_comm (m • h) G']
    exact hxy_eq.trans (Form.MisereQuotient.add_misereEQ_add
      (isLde_nsmul hh m).shortDeadEnding hG'lde.shortDeadEnding hGH.symm (fun _ _ => rfl))
  exact ihn m (by omega) hm g h hg hh
    (lde_cancellative (isLde_nsmul hg m) (isLde_nsmul hh m) hG'lde hstep)
termination_by g
decreasing_by form_wf

/--
If $G$ and $H$ are Left dead ends with $n \cdot G = n \cdot H$ for some $n > 0$, then
$G = H$.

This is [Davies (Proposition 3.8 on p. 13)][davies:FactorisationsLeftDead:2024].
-/
theorem lde_nsmul_cancel {g h : GameForm} (hg : IsLde g) (hh : IsLde h) {n : ℕ} (hn : 0 < n)
    (heq : (n • g) ≡ₗ (n • h)) : g ≡ₗ h := by
  have key : ∀ n : ℕ, 0 < n → ∀ a b : GameForm, IsLde a → IsLde b →
      ((n • a) ≡ₗ (n • b)) → a ≡ₗ b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn => exact fun hn' => lde_nsmul_cancel_step hn' ihn
  exact key n hn g h hg hh heq

/-- This is [Davies (Open problem E.1 on p. 49)][davies:FactorisationsLeftDead:2024]. -/
def pocancellativeNotInvertible (A : GameForm → Prop) : Set GameForm :=
  {j | A j ∧ IsPocancellativeIn A j ∧ ¬ ∃ k, A k ∧ MisereEQ A (j + k) 0}

/-! ## Divisibility, atoms, primes and factorisations -/

@[expose] def LdeDvd (g h : GameForm) : Prop := ∃ k, IsLde k ∧ (h ≡ₗ (g + k))

@[expose] def IsLdeAtom (g : GameForm) : Prop :=
  IsLde g ∧ g ≠ 0 ∧
    ∀ h k, IsLde h → IsLde k → (g ≡ₗ (h + k)) → h = 0 ∨ k = 0

/--
In a monoid $M$, we call a non-invertible element $m \in M$ a *molecule* if $m$ is atomic
but not an atom.

This is [Davies (Definition 2.6 on p. 9)][davies:FactorisationsLeftDead:2024].
-/
@[expose] def IsMolecule (g : GameForm) : Prop := IsLde g ∧ g ≠ 0 ∧ ¬ IsLdeAtom g

@[expose] def IsLdePrime (p : GameForm) : Prop :=
  IsLde p ∧ p ≠ 0 ∧
    ∀ h k, IsLde h → IsLde k → LdeDvd p (h + k) → LdeDvd p h ∨ LdeDvd p k

@[expose] def IsFactorisation (s : Multiset GameForm) (g : GameForm) : Prop :=
  (∀ a ∈ s, IsLdeAtom a) ∧ (s.sum ≡ₗ g)

@[expose] def UniquelyFactorisable (g : GameForm) : Prop :=
  ∀ s t : Multiset GameForm, IsFactorisation s g → IsFactorisation t g →
    Multiset.Rel (MisereEQ Form.DeadEnding.ShortDeadEnding) s t

@[expose] def IsPrimeFactorisable (g : GameForm) : Prop :=
  ∃ s : Multiset GameForm, (∀ a ∈ s, IsLdePrime a) ∧ (s.sum ≡ₗ g)

private theorem lde_atomic_aux (n : ℕ) :
    ∀ g : GameForm, IsLde g → race g ≤ n → ∃ s, IsFactorisation s g := by
  induction n with
  | zero =>
    intro g hg hle
    have hg0 : g = 0 := (lde_race_zero_iff hg).mp (Nat.le_zero.mp hle)
    exact ⟨0, by simp, by rw [Multiset.sum_zero, hg0]; exact fun _ _ => rfl⟩
  | succ n ih =>
    intro g hg hle
    by_cases hg0 : g = 0
    · exact ⟨0, by simp, by rw [Multiset.sum_zero, hg0]; exact fun _ _ => rfl⟩
    by_cases hatom : IsLdeAtom g
    · refine ⟨{g}, fun a ha => ?_, ?_⟩
      · rw [Multiset.mem_singleton.mp ha]
        exact hatom
      · rw [Multiset.sum_singleton]
        exact fun _ _ => rfl
    have h_split : ∃ h k, IsLde h ∧ IsLde k ∧ (g ≡ₗ (h + k)) ∧ h ≠ 0 ∧ k ≠ 0 := by
      by_contra hc
      refine hatom ⟨hg, hg0, fun h k hh hk heq => ?_⟩
      by_cases hh0 : h = 0
      · exact Or.inl hh0
      · by_cases hk0 : k = 0
        · exact Or.inr hk0
        · exact absurd ⟨h, k, hh, hk, heq, hh0, hk0⟩ hc
    obtain ⟨h, k, hh, hk, heq, hh0, hk0⟩ := h_split
    have h_race : race h + race k ≤ n + 1 := by
      rw [← race_add hh hk, ← race_eq_of_misereEQ hg (hh.add hk) heq]
      exact hle
    have h_race_h : 1 ≤ race h := Nat.one_le_iff_ne_zero.mpr
      fun hc => hh0 ((lde_race_zero_iff hh).mp hc)
    have h_race_k : 1 ≤ race k := Nat.one_le_iff_ne_zero.mpr
      fun hc => hk0 ((lde_race_zero_iff hk).mp hc)
    obtain ⟨s, hs_atoms, hs_sum⟩ := ih h hh (by omega)
    obtain ⟨t, ht_atoms, ht_sum⟩ := ih k hk (by omega)
    refine ⟨s + t, fun a ha => ?_, ?_⟩
    · rcases Multiset.mem_add.mp ha with ha' | ha'
      · exact hs_atoms a ha'
      · exact ht_atoms a ha'
    · rw [Multiset.sum_add]
      exact (Form.MisereQuotient.add_misereEQ_add
        (isLde_sum fun b hb => (ht_atoms b hb).1).shortDeadEnding
        hh.shortDeadEnding hs_sum ht_sum).trans heq.symm

/--
The monoid of Left dead ends $\mathcal{L}$ is atomic.

This is [Davies (Lemma 3.23 on p. 19)][davies:FactorisationsLeftDead:2024].
-/
theorem lde_atomic {g : GameForm} (hg : IsLde g) : ∃ s, IsFactorisation s g :=
  lde_atomic_aux (race g) g hg le_rfl

/--
If $G$, $H$, and $K$ are non-zero Left dead ends with $G = H + K$, then $b(H) < b(G)$.

This is [Davies (Lemma 3.22 on p. 19)][davies:FactorisationsLeftDead:2024].
-/
theorem birthday_lt_of_add {g h k : GameForm} (hg : IsLde g) (hh : IsLde h) (hk : IsLde k)
    (hk0 : k ≠ 0) (heq : g ≡ₗ (h + k)) : birthday h < birthday g := by
  rw [birthday_eq_of_misereEQ hg (hh.add hk) heq, birthday_add]
  exact lt_add_of_pos_right _ (birthday_pos_of_ne_zero hk hk0)

theorem card_le_race_sum {s : Multiset GameForm} (hs : ∀ a ∈ s, IsLdeAtom a) :
    Multiset.card s ≤ race s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ b ∈ s, IsLdeAtom b := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    have h_sum_lde : IsLde s.sum := isLde_sum fun b hb => (hs' b hb).1
    have h_race_a : 1 ≤ race a := by
      rcases Nat.eq_zero_or_pos (race a) with h_zero | h_pos
      · exact absurd ((lde_race_zero_iff ha.1).mp h_zero) ha.2.1
      · exact h_pos
    have h_ih := ih hs'
    rw [Multiset.sum_cons, Multiset.card_cons, race_add ha.1 h_sum_lde]
    omega

/--
The monoid of Left dead ends $\mathcal{L}$ is a BF-monoid. In particular, if $G$ is a Left
dead end, then the length of each factorisation of $G$ is at most $r(G)$; that is,
$\overline{\mathsf{L}(G)} \le r(G)$.

This is [Davies (Lemma 3.24 on p. 19)][davies:FactorisationsLeftDead:2024].
-/
theorem factorisation_length_le_race {g : GameForm} (hg : IsLde g)
    {s : Multiset GameForm} (hs : IsFactorisation s g) : Multiset.card s ≤ race g := by
  have h_lde : ∀ a ∈ s, IsLde a := fun a ha => (hs.1 a ha).1
  rw [← race_eq_of_misereEQ (isLde_sum h_lde) hg hs.2]
  exact card_le_race_sum hs.1

/--
If $G$ is a Left dead end with $r(G) = 1$, then $G$ is an atom.

This is [Davies (Corollary 3.25 on p. 20)][davies:FactorisationsLeftDead:2024].
-/
theorem lde_atom_of_race_one {g : GameForm} (hg : IsLde g) (hr : race g = 1) :
    IsLdeAtom g := by
  have hg0 : g ≠ 0 := by
    intro hc
    rw [(lde_race_zero_iff hg).mpr hc] at hr
    exact absurd hr (by decide)
  refine ⟨hg, hg0, fun h k hh hk heq => ?_⟩
  have h_race := race_eq_of_misereEQ hg (hh.add hk) heq
  rw [race_add hh hk, hr] at h_race
  by_cases hh0 : h = 0
  · exact Or.inl hh0
  · refine Or.inr ((lde_race_zero_iff hk).mp ?_)
    have h_race_h : race h ≠ 0 := fun hc => hh0 ((lde_race_zero_iff hh).mp hc)
    omega

theorem IsLdeAtom.of_misereEQ {a g : GameForm} (ha : IsLdeAtom a) (hg : IsLde g)
    (heq : a ≡ₗ g) : IsLdeAtom g :=
  ⟨hg, fun hc => ha.2.1 ((lde_misereEQ_zero_iff ha.1).mp (by rw [hc] at heq; exact heq)),
    fun h k hh hk hsum => ha.2.2 h k hh hk (heq.trans hsum)⟩

/--
The monoid of Left dead ends $\mathcal{L}$ is an FF-monoid.

This is [Davies (Theorem 3.26 on p. 20)][davies:FactorisationsLeftDead:2024].
-/
theorem lde_ff {g : GameForm} (hg : IsLde g) :
    { s : Multiset GameForm | IsFactorisation s g }.Finite := by
  obtain ⟨N, hN⟩ := short_iff_birthday_nat.mp hg.short
  have hS_fin : {x : GameForm | birthday x ≤ N}.Finite := GameForm.finite_setOf_birthday_le N
  have : Finite {x : GameForm // birthday x ≤ N} := hS_fin.to_subtype
  have h_dom_fin : {l : List {x : GameForm // birthday x ≤ N} | l.length ≤ race g}.Finite :=
    List.finite_length_le _ (race g)
  have h_img_fin :
      ((fun l : List {x : GameForm // birthday x ≤ N} => (↑(l.map Subtype.val) : Multiset GameForm))
        '' {l : List {x : GameForm // birthday x ≤ N} | l.length ≤ race g}).Finite :=
    h_dom_fin.image _
  refine h_img_fin.subset ?_
  intro s hs
  obtain ⟨hs_atoms, hs_sum⟩ := hs
  have h_sub_S : ∀ a ∈ s, birthday a ≤ (N : NatOrdinal) := by
    intro a ha
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
    have h_lde_rest : IsLde t.sum :=
      isLde_sum fun b hb => (hs_atoms b (ht ▸ Multiset.mem_cons_of_mem hb)).1
    have h_lde_s : IsLde s.sum := isLde_sum fun b hb => (hs_atoms b hb).1
    have h_sum_eq : s.sum = a + t.sum := by rw [ht, Multiset.sum_cons]
    have h_le : birthday a ≤ birthday s.sum := by
      rw [h_sum_eq, birthday_add]
      exact le_add_of_nonneg_right (by simp)
    rwa [birthday_eq_of_misereEQ h_lde_s hg hs_sum, hN] at h_le
  have h_card : s.card ≤ race g := factorisation_length_le_race hg ⟨hs_atoms, hs_sum⟩
  refine ⟨s.toList.pmap (fun a ha => (⟨a, h_sub_S a (Multiset.mem_toList.mp ha)⟩ :
    {x : GameForm // birthday x ≤ N})) (fun a ha => ha), ?_, ?_⟩
  · simpa [List.length_pmap, Multiset.length_toList] using h_card
  · simp [Multiset.coe_toList]

/-! ## The prime $\overline{1}$ -/

/--
If $G$ is a Left dead end, then $\overline{1} + G' \ge G$ for every option $G'$ of $G$.

This is [Davies (Lemma 4.1 on p. 20)][davies:FactorisationsLeftDead:2024].
-/
theorem neg_one_add_option_ge {g gr : GameForm} (hg : IsLde g) (hgr : gr ∈ moves .right g) :
    (-(1 : GameForm) + gr) ≥ₗ g := by
  have hgr_lde : IsLde gr := hg.of_mem_rightMoves hgr
  rw [misereGE_lde_iff ((isLde_neg_one).add hgr_lde) hg]
  refine ⟨fun h_end => absurd h_end ?_, fun x hx => ⟨gr, hgr, ?_⟩⟩
  · rw [isEnd_def, moves_add, rightMoves_neg_one]
    exact (Set.Nonempty.inl ((Set.singleton_nonempty (0 : GameForm)).image _)).ne_empty
  · rw [moves_add, rightMoves_neg_one] at hx
    simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hx
    rcases hx with ⟨_, rfl, rfl⟩ | ⟨gr', hgr'_mem, rfl⟩
    · rw [zero_add]
      exact MisereGE.refl gr
    · exact neg_one_add_option_ge hgr_lde hgr'_mem
termination_by g
decreasing_by form_wf

theorem isLde_singletonRight {g : GameForm} (hg : IsLde g) :
    IsLde (!{(∅ : Set GameForm) | {g}}) := by
  refine ⟨IsShort.ofSets Set.finite_empty (by simp) (Set.finite_singleton g)
    (by simpa using hg.short), ?_⟩
  rw [isDeadEnd_def]
  refine ⟨by rw [isEnd_def]; simp, fun gp hgp => ?_⟩
  rw [moves_ofSets] at hgp
  simp only [Player.cases, Set.mem_singleton_iff] at hgp
  subst hgp
  exact hg.deadEnd

theorem rightMoves_singletonRight {g : GameForm} :
    moves .right (!{(∅ : Set GameForm) | {g}}) = {g} := by simp

/--
If $G$ is a Left dead end, then $\overline{1} + G = \{\cdot \mid G\}$.

This is [Davies (Proposition 4.2 on p. 21)][davies:FactorisationsLeftDead:2024].
-/
theorem neg_one_add_eq_singleton {g : GameForm} (hg : IsLde g) :
    (-(1 : GameForm) + g) ≡ₗ !{(∅ : Set GameForm) | {g}} := by
  have hS_lde : IsLde !{(∅ : Set GameForm) | {g}} := isLde_singletonRight hg
  have hS_right : moves .right (!{(∅ : Set GameForm) | {g}}) = {g} := rightMoves_singletonRight
  have h1 : (-(1 : GameForm) + g) ≥ₗ !{(∅ : Set GameForm) | {g}} := by
    rw [misereGE_lde_iff ((isLde_neg_one).add hg) hS_lde]
    refine ⟨fun h_end => absurd h_end ?_, fun x hx => ?_⟩
    · rw [isEnd_def, moves_add, rightMoves_neg_one]
      exact (Set.Nonempty.inl ((Set.singleton_nonempty (0 : GameForm)).image _)).ne_empty
    · rw [moves_add, rightMoves_neg_one] at hx
      simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hx
      rw [hS_right]
      rcases hx with ⟨_, rfl, rfl⟩ | ⟨g', hg'_mem, rfl⟩
      · exact ⟨g, rfl, by rw [zero_add]; exact MisereGE.refl g⟩
      · exact ⟨g, rfl, neg_one_add_option_ge hg hg'_mem⟩
  have h2 : !{(∅ : Set GameForm) | {g}} ≥ₗ (-(1 : GameForm) + g) := by
    rw [misereGE_lde_iff hS_lde ((isLde_neg_one).add hg)]
    refine ⟨fun h_end => absurd h_end ?_, fun x hx => ?_⟩
    · rw [isEnd_def, hS_right]
      exact (Set.singleton_nonempty g).ne_empty
    · rw [hS_right] at hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      refine ⟨g, ?_, MisereGE.refl g⟩
      rw [moves_add, rightMoves_neg_one]
      exact Or.inl ⟨0, rfl, zero_add g⟩
  intro x hx
  exact le_antisymm (h2 x hx) (h1 x hx)

/--
If $G$ and $G'$ are Left dead ends, then $G$ has exactly one good option (equal to) $G'$
if and only if $G = \overline{1} + G'$.

This is [Davies (Proposition 4.3 on p. 21)][davies:FactorisationsLeftDead:2024].
-/
theorem unique_good_option_iff {g gr : GameForm} (hg : IsLde g) (hgr : IsLde gr) :
    (∃ x, IsGoodOption x g ∧ x ≡ₗ gr ∧ ∀ y, IsGoodOption y g → y ≡ₗ gr) ↔
      (g ≡ₗ (-(1 : GameForm) + gr)) := by
  have hS_lde : IsLde !{(∅ : Set GameForm) | {gr}} := isLde_singletonRight hgr
  have hS_right : moves .right (!{(∅ : Set GameForm) | {gr}}) = {gr} :=
    rightMoves_singletonRight
  constructor
  · rintro ⟨x, hx_good, hx_eq, hx_uniq⟩
    have h1 : (!{(∅ : Set GameForm) | {gr}}) ≥ₗ g := by
      rw [misereGE_lde_iff hS_lde hg]
      refine ⟨fun h_end => absurd h_end ?_, fun y hy => ?_⟩
      · rw [isEnd_def, hS_right]
        exact (Set.singleton_nonempty gr).ne_empty
      · rw [hS_right] at hy
        simp only [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨x, hx_good.1, misereGE_of_misereEQ hx_eq.symm⟩
    have h2 : g ≥ₗ !{(∅ : Set GameForm) | {gr}} := by
      rw [misereGE_lde_iff hg hS_lde]
      refine ⟨fun h_end => absurd h_end ?_, fun y hy => ?_⟩
      · rw [isEnd_def]
        exact (Set.nonempty_of_mem hx_good.1).ne_empty
      · rw [hS_right]
        obtain ⟨y', hy'_good, hy_ge_y'⟩ := exists_isGoodOption_le_of_mem_rightMoves hg hy
        exact ⟨gr, rfl, hy_ge_y'.trans (misereGE_of_misereEQ (hx_uniq y' hy'_good))⟩
    exact (MisereEq.of_antisymm h2 h1).trans (neg_one_add_eq_singleton hgr).symm
  · intro heq
    have h_gS : g ≡ₗ !{(∅ : Set GameForm) | {gr}} := heq.trans (neg_one_add_eq_singleton hgr)
    have hgr_good_S : IsGoodOption gr (!{(∅ : Set GameForm) | {gr}}) := by
      refine ⟨by rw [hS_right]; exact Set.mem_singleton_iff.mpr rfl, ?_⟩
      rintro ⟨z, hz_mem, hz_gt⟩
      rw [hS_right, Set.mem_singleton_iff] at hz_mem
      exact hz_gt.2 (hz_mem ▸ MisereGE.refl z)
    obtain ⟨x, hx_good, hgr_ge_x⟩ :=
      lde_good_option_dominates hS_lde hg (misereGE_of_misereEQ h_gS.symm) hgr_good_S
    obtain ⟨z, hz_good, hx_ge_z⟩ :=
      lde_good_option_dominates hg hS_lde (misereGE_of_misereEQ h_gS) hx_good
    have hz_eq : z = gr := by
      have hmem := hz_good.1
      rwa [hS_right, Set.mem_singleton_iff] at hmem
    rw [hz_eq] at hx_ge_z
    have hx_eq : x ≡ₗ gr := MisereEq.of_antisymm hx_ge_z hgr_ge_x
    refine ⟨x, hx_good, hx_eq, fun y hy_good => ?_⟩
    obtain ⟨w, hw_good, hy_ge_w⟩ :=
      lde_good_option_dominates hg hS_lde (misereGE_of_misereEQ h_gS) hy_good
    have hw_eq : w = gr := by
      have hmem := hw_good.1
      rwa [hS_right, Set.mem_singleton_iff] at hmem
    rw [hw_eq] at hy_ge_w
    have hx_ge_y : x ≥ₗ y := by
      by_contra hnx
      exact hy_good.2 ⟨x, hx_good.1, hy_ge_w.trans (misereGE_of_misereEQ hx_eq.symm), hnx⟩
    exact MisereEq.of_antisymm hy_ge_w (hgr_ge_x.trans hx_ge_y)

/--
The game $\overline{1}$ is prime in the monoid of Left dead ends $\mathcal{L}$.

This is [Davies (Theorem 4.4 on p. 21)][davies:FactorisationsLeftDead:2024].
-/
theorem neg_one_prime : IsLdePrime (-(1 : GameForm)) := by
  refine ⟨isLde_neg_one, ?_, ?_⟩
  · intro hc
    have hmem : (0 : GameForm) ∈ moves .right (-(1 : GameForm)) := by rw [rightMoves_neg_one]; rfl
    rw [hc, moves_zero] at hmem
    exact Set.notMem_empty _ hmem
  · rintro h k hh hk ⟨G, hG, hdvd⟩
    have hhk : IsLde (h + k) := hh.add hk
    have hne : h + k ≠ 0 := by
      intro hc
      rw [hc] at hdvd
      have h0 : -(1 : GameForm) + G = 0 :=
        (lde_misereEQ_zero_iff (isLde_neg_one.add hG)).mp hdvd.symm
      have hmem : (0 : GameForm) + G ∈ moves .right (-(1 : GameForm) + G) := by
        rw [moves_add]
        exact Or.inl ⟨0, by rw [rightMoves_neg_one]; rfl, rfl⟩
      rw [h0, moves_zero] at hmem
      exact Set.notMem_empty _ hmem
    -- `h + k ≡ 1 + G` has a unique good option (Prop 4.3), so *its* good option `w`
    -- satisfies `w ≡ G`, hence `h + k ≡ 1 + w`.
    obtain ⟨w₀, hw₀⟩ := hhk.rightMoves_nonempty hne
    obtain ⟨w, hw_good, -⟩ := exists_isGoodOption_le_of_mem_rightMoves hhk hw₀
    obtain ⟨-, -, -, huniq⟩ := (unique_good_option_iff hhk hG).mpr hdvd
    have hkey : (h + k) ≡ₗ (-(1 : GameForm) + w) :=
      hdvd.trans (Form.MisereQuotient.add_misereEQ_add hG.shortDeadEnding
        (isLde_neg_one).shortDeadEnding (fun _ _ => rfl) (huniq w hw_good).symm)
    have hmem := hw_good.1
    rw [moves_add] at hmem
    simp only [Set.mem_union, Set.mem_image] at hmem
    rcases hmem with ⟨h', hh'_mem, rfl⟩ | ⟨k', hk'_mem, rfl⟩
    · refine Or.inl ⟨h', hh.of_mem_rightMoves hh'_mem, ?_⟩
      refine lde_cancellative hh ((isLde_neg_one).add (hh.of_mem_rightMoves hh'_mem)) hk ?_
      rw [add_assoc]
      exact hkey
    · refine Or.inr ⟨k', hk.of_mem_rightMoves hk'_mem, ?_⟩
      refine lde_cancellative hk ((isLde_neg_one).add (hk.of_mem_rightMoves hk'_mem)) hh ?_
      rw [add_comm k h, add_assoc, add_comm k' h]
      exact hkey

theorem neg_intCast_add (a b : ℕ) :
    -((a + b : ℕ) : GameForm) = -(a : GameForm) + -(b : GameForm) := by
  rw [Nat.cast_add, neg_add]

theorem neg_intCast_injective : Function.Injective (fun n : ℕ => -(n : GameForm)) := by
  intro a b hab
  have h := congrArg terminalLengths hab
  rw [terminalLengths_neg_intCast, terminalLengths_neg_intCast] at h
  exact Set.singleton_injective h

@[simp]
theorem neg_intCast_eq_zero_iff {n : ℕ} : -(n : GameForm) = 0 ↔ n = 0 :=
  ⟨fun h => neg_intCast_injective
    (show -(n : GameForm) = -((0 : ℕ) : GameForm) by rw [h, Nat.cast_zero, neg_zero]),
    fun h => by simp [h]⟩

theorem nsmul_neg_one : ∀ n : ℕ, n • -(1 : GameForm) = -(n : GameForm)
  | 0 => by rw [zero_nsmul, Nat.cast_zero, neg_zero]
  | n + 1 => by
    rw [succ_nsmul, nsmul_neg_one n, ← Nat.cast_one (R := GameForm), ← neg_intCast_add]

theorem neg_intCast_eq_of_misereEQ {a b : ℕ}
    (hab : -(a : GameForm) ≡ₗ -(b : GameForm)) : a = b := by
  have h := terminalLengths_eq_of_misereEQ (isLde_neg_intCast a) (isLde_neg_intCast b) hab
  rw [terminalLengths_neg_intCast, terminalLengths_neg_intCast] at h
  exact Set.singleton_injective h

theorem eq_neg_one_of_isLdeAtom_of_isInteger {a : GameForm} (ha : IsLdeAtom a)
    (hi : IsInteger a) : a = -(1 : GameForm) := by
  obtain ⟨m, rfl⟩ := exists_eq_neg_intCast_of_isInteger ha.1 hi
  have hm0 : m ≠ 0 := fun hc => ha.2.1 (by rw [hc]; simp)
  by_contra hne
  have hm1 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · exact absurd
        (by rw [show m = 1 by omega, Nat.cast_one] : -(m : GameForm) = -(1 : GameForm)) hne
    · exact h
  obtain ⟨j, rfl⟩ : ∃ j, m = 1 + j := ⟨m - 1, by omega⟩
  rcases ha.2.2 (-(1 : GameForm)) (-(j : GameForm)) (isLde_neg_one) (isLde_neg_intCast j)
    (by rw [neg_intCast_add, Nat.cast_one]; exact fun _ _ => rfl) with hc | hc
  · exact absurd hc (neg_ne_zero.mpr one_ne_zero)
  · have hj := neg_intCast_eq_zero_iff.mp hc
    omega

theorem eq_replicate_of_isFactorisation_neg_intCast {n : ℕ} {s : Multiset GameForm}
    (hs : IsFactorisation s (-(n : GameForm))) : s = Multiset.replicate n (-(1 : GameForm)) := by
  have hs_lde : ∀ a ∈ s, IsLde a := fun a ha => (hs.1 a ha).1
  have hsum_lde : IsLde s.sum := isLde_sum hs_lde
  have hall : ∀ a ∈ s, a = -(1 : GameForm) := by
    intro a ha
    refine eq_neg_one_of_isLdeAtom_of_isInteger (hs.1 a ha) ?_
    obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem ha
    have hrest : IsLde u.sum :=
      isLde_sum fun b hb => hs_lde b (by rw [hu]; exact Multiset.mem_cons_of_mem hb)
    have hsplit : s.sum = a + u.sum := by rw [hu, Multiset.sum_cons]
    have hT : { x + y | (x ∈ terminalLengths a) (y ∈ terminalLengths u.sum) } = {n} := by
      rw [← terminalLengths_add (hs_lde a ha) hrest, ← hsplit,
        terminalLengths_eq_of_misereEQ hsum_lde (isLde_neg_intCast n) hs.2,
        terminalLengths_neg_intCast]
    obtain ⟨y, hy⟩ := (terminalLengths_finite_nonempty hrest).2
    refine (isInteger_iff_terminalLengths_subsingleton (hs_lde a ha)).mpr fun x hx x' hx' => ?_
    have h1 : x + y ∈ ({n} : Set ℕ) := hT ▸ ⟨x, hx, y, hy, rfl⟩
    have h2 : x' + y ∈ ({n} : Set ℕ) := hT ▸ ⟨x', hx', y, hy, rfl⟩
    simp only [Set.mem_singleton_iff] at h1 h2
    omega
  have hrep : s = Multiset.replicate (Multiset.card s) (-(1 : GameForm)) :=
    Multiset.eq_replicate_card.mpr hall
  have hcard : Multiset.card s = n := by
    refine neg_intCast_eq_of_misereEQ (a := Multiset.card s) ?_
    rw [← nsmul_neg_one, ← Multiset.sum_replicate, ← hrep]
    exact hs.2
  rw [hrep, hcard]

theorem neg_intCast_uniquelyFactorisable (n : ℕ) : UniquelyFactorisable (-(n : GameForm)) := by
  intro s t hs ht
  rw [eq_replicate_of_isFactorisation_neg_intCast hs,
    eq_replicate_of_isFactorisation_neg_intCast ht]
  exact Multiset.rel_refl_of_refl_on fun _ _ _ _ => rfl

theorem neg_intCast_ge_of_mem_terminalLengths {y : GameForm} (hy : IsLde y) {k : ℕ}
    (hk : k ∈ terminalLengths y) : -(k : GameForm) ≥ₗ y := by
  by_cases hy0 : y = 0
  · subst hy0
    rw [terminalLengths_zero, Set.mem_singleton_iff] at hk
    subst hk
    have h_neg_zero : -((0 : ℕ) : GameForm) = (0 : GameForm) := by simp
    rw [h_neg_zero]
    exact MisereGE.refl 0
  · rw [terminalLengths_of_ne_zero hy0] at hk
    simp only [Set.mem_iUnion, Set.mem_image] at hk
    obtain ⟨yr, hyr_mem, k', hk'_mem, hk_eq⟩ := hk
    subst hk_eq
    rw [misereGE_lde_iff (isLde_neg_intCast (k' + 1)) hy]
    refine ⟨fun h_end => absurd h_end ?_, fun x hx => ?_⟩
    · rw [isEnd_def, rightMoves_neg_intCast_succ]
      exact (Set.singleton_nonempty _).ne_empty
    · rw [rightMoves_neg_intCast_succ] at hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨yr, hyr_mem,
        neg_intCast_ge_of_mem_terminalLengths (hy.of_mem_rightMoves hyr_mem) hk'_mem⟩
termination_by y
decreasing_by form_wf

/-- This is [Davies (Open problem 4.5 on p. 22)][davies:FactorisationsLeftDead:2024]. -/
def LdeOtherPrimeProblem : Prop :=
  ∃ p : GameForm.{u}, IsLdePrime p ∧ ¬ (p ≡ₗ -(1 : GameForm))

/-- This is [Davies (Open problem 4.5 on p. 22)][davies:FactorisationsLeftDead:2024]. -/
def LdeNonPrimeAtomProblem : Prop :=
  ∃ a : GameForm.{u}, IsLdeAtom a ∧ ¬ IsLdePrime a

/-! ## Flexibility and the atom criteria -/

private theorem isInteger_of_mem_rightMoves_of_flexibility_le_one {g gr : GameForm}
    (hg : IsLde g) (hgi : ¬ IsInteger g) (hf : flexibility g ≤ 1) (hgr : gr ∈ moves .right g) :
    IsInteger gr := by
  by_contra hgri
  have h := flexibility_succ_le_of_mem_rightMoves hg hgi hgr
  rw [flexibility_of_not_isInteger hgri] at h
  omega

/--
If $G$ and $H$ are Left dead ends with $f(G) \le 1$ and $T(G) \subseteq T(H)$, then
$G \ge H$.

This is [Davies (Proposition 5.2 on p. 23)][davies:FactorisationsLeftDead:2024].
-/
theorem ge_of_flexibility_le_one {g h : GameForm} (hg : IsLde g) (hh : IsLde h)
    (hf : flexibility g ≤ 1) (hT : terminalLengths g ⊆ terminalLengths h) : g ≥ₗ h := by
  by_cases hgi : IsInteger g
  · obtain ⟨n, rfl⟩ := exists_eq_neg_intCast_of_isInteger hg hgi
    have hn_mem : n ∈ terminalLengths h := hT (by rw [terminalLengths_neg_intCast]; rfl)
    exact neg_intCast_ge_of_mem_terminalLengths hh hn_mem
  · have hg0 : g ≠ 0 := fun hc => hgi (hc ▸ ⟨0, by simp⟩)
    rw [misereGE_lde_iff hg hh]
    refine ⟨fun h_end => absurd h_end ?_, fun x hx => ?_⟩
    · rw [isEnd_def]
      exact (hg.rightMoves_nonempty hg0).ne_empty
    · obtain ⟨m, hm⟩ := exists_eq_neg_intCast_of_isInteger (hg.of_mem_rightMoves hx)
        (isInteger_of_mem_rightMoves_of_flexibility_le_one hg hgi hf hx)
      subst hm
      have hmem_g : m + 1 ∈ terminalLengths g := by
        rw [terminalLengths_of_ne_zero hg0]
        simp only [Set.mem_iUnion, Set.mem_image]
        exact ⟨-(m : GameForm), hx, m, by rw [terminalLengths_neg_intCast]; rfl, rfl⟩
      have hmem_h := hT hmem_g
      have hh0 : h ≠ 0 := by
        intro hc
        rw [hc, terminalLengths_zero] at hmem_h
        simp at hmem_h
      rw [terminalLengths_of_ne_zero hh0] at hmem_h
      simp only [Set.mem_iUnion, Set.mem_image] at hmem_h
      obtain ⟨hr, hhr_mem, t, ht_mem, ht_eq⟩ := hmem_h
      have ht_eq' : t = m := by omega
      subst ht_eq'
      exact ⟨hr, hhr_mem,
        neg_intCast_ge_of_mem_terminalLengths (hh.of_mem_rightMoves hhr_mem) ht_mem⟩

/--
If $G$ is a Left dead end, then we say an option $G'$ of $G$ is *versatile* if
$f(G') \ge f(G) - 1$.

This is [Davies (Definition 5.3 on p. 23)][davies:FactorisationsLeftDead:2024].
-/
@[expose] def IsVersatileOption (gr g : GameForm) : Prop :=
  gr ∈ moves .right g ∧ flexibility g ≤ flexibility gr + 1

theorem exists_isVersatileOption {g : GameForm} (hg : IsLde g) (hg0 : g ≠ 0) :
    ∃ gr, IsVersatileOption gr g := by
  by_cases hgi : IsInteger g
  · obtain ⟨gr, hgr⟩ := hg.rightMoves_nonempty hg0
    exact ⟨gr, hgr, by rw [flexibility_of_isInteger hgi]; omega⟩
  · have h_fin : ((fun x => flexibility x) '' moves .right g).Finite :=
      (IsShort.finite_moves .right hg.short).image _
    have h_ne : ((fun x => flexibility x) '' moves .right g).Nonempty :=
      (hg.rightMoves_nonempty hg0).image _
    obtain ⟨gr, hgr_mem, hgr_eq⟩ := Nat.sSup_mem h_ne h_fin.bddAbove
    dsimp only at hgr_eq
    refine ⟨gr, hgr_mem, ?_⟩
    rw [flexibility_of_not_isInteger hgi, hgr_eq]
    omega

theorem flexibility_eq_of_isVersatileOption {g gr : GameForm} (hg : IsLde g)
    (hgi : ¬ IsInteger g) (hgr : IsVersatileOption gr g) :
    flexibility g = flexibility gr + 1 := by
  have h_le := flexibility_succ_le_of_mem_rightMoves hg hgi hgr.1
  have hf := hgr.2
  omega

theorem two_le_sSup_terminalLengths {g : GameForm} (hg : IsLde g) (hg0 : g ≠ 0)
    (hgi : ¬ IsInteger g) : 2 ≤ sSup (terminalLengths g) := by
  have h1 : 1 ≤ race g :=
    Nat.one_le_iff_ne_zero.mpr fun hc => hg0 ((lde_race_zero_iff hg).mp hc)
  have h2 := race_lt_sSup_terminalLengths hg hgi
  omega

/-- See `flexibility_le_birthday`. -/
theorem flexibility_lt_birthday_of_ne_zero {g : GameForm} (hg : IsLde g) (hg0 : g ≠ 0) :
    (flexibility g : NatOrdinal) < birthday g := by
  by_cases hgi : IsInteger g
  · rw [flexibility_of_isInteger hgi, Nat.cast_zero]
    exact birthday_pos_of_ne_zero hg hg0
  · obtain ⟨gr, hgr⟩ := exists_isVersatileOption hg hg0
    have hf := flexibility_eq_of_isVersatileOption hg hgi hgr
    by_cases hgr0 : gr = 0
    · have h2 := two_le_sSup_terminalLengths hg hg0 hgi
      rw [hf, hgr0, flexibility_of_isInteger ⟨0, by simp⟩, birthday_eq_sSup_terminalLengths hg]
      exact_mod_cast h2
    · have hih := flexibility_lt_birthday_of_ne_zero (hg.of_mem_rightMoves hgr.1) hgr0
      have hlt : birthday gr < birthday g := birthday_lt_of_mem_moves hgr.1
      rw [hf, Nat.cast_add, Nat.cast_one]
      exact lt_of_le_of_lt (Order.add_one_le_of_lt hih) hlt
termination_by g
decreasing_by exact Moves.Subposition.of_mem_moves hgr.1

/--
If $G$ is a Left dead end, then $f(G) \le b(G)$, with equality if and only if $G = 0$.

This is [Davies (Lemma 5.4 on p. 24)][davies:FactorisationsLeftDead:2024].
-/
theorem flexibility_le_birthday {g : GameForm} (hg : IsLde g) :
    (flexibility g : NatOrdinal) ≤ birthday g := by
  by_cases hg0 : g = 0
  · subst hg0
    rw [flexibility_of_isInteger ⟨0, by simp⟩, birthday_zero, Nat.cast_zero]
  · exact (flexibility_lt_birthday_of_ne_zero hg hg0).le

/-- See `flexibility_le_birthday`. -/
theorem flexibility_eq_birthday_iff {g : GameForm} (hg : IsLde g) :
    (flexibility g : NatOrdinal) = birthday g ↔ g = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hg0
    exact absurd h (flexibility_lt_birthday_of_ne_zero hg hg0).ne
  · subst h
    rw [flexibility_of_isInteger ⟨0, by simp⟩, birthday_zero, Nat.cast_zero]

/--
If $G$ and $H$ are Left dead ends with $G \ge H$, then $f(G) \le f(H)$.

This is [Davies (Proposition 5.5 on p. 24)][davies:FactorisationsLeftDead:2024].
-/
theorem flexibility_le_of_ge {g h : GameForm} (hg : IsLde g) (hh : IsLde h) (hge : g ≥ₗ h) :
    flexibility g ≤ flexibility h := by
  by_cases hgi : IsInteger g
  · rw [flexibility_of_isInteger hgi]
    exact Nat.zero_le _
  · have hg0 : g ≠ 0 := fun hc => hgi (hc ▸ ⟨0, by simp⟩)
    have hhi : ¬ IsInteger h := by
      intro hhi_int
      obtain ⟨n, rfl⟩ := exists_eq_neg_intCast_of_isInteger hh hhi_int
      have hsub : terminalLengths g ⊆ {n} := by
        have h_sub := terminalLengths_subset_of_ge hg hh hge
        rwa [terminalLengths_neg_intCast] at h_sub
      have hsub_g : (terminalLengths g).Subsingleton := fun a ha b hb => by
        have ha' := hsub ha
        have hb' := hsub hb
        simp only [Set.mem_singleton_iff] at ha' hb'
        omega
      exact hgi ((isInteger_iff_terminalLengths_subsingleton hg).mpr hsub_g)
    have h_fin_g : ((fun x => flexibility x) '' moves .right g).Finite :=
      (IsShort.finite_moves .right hg.short).image _
    have h_ne_g : ((fun x => flexibility x) '' moves .right g).Nonempty :=
      (hg.rightMoves_nonempty hg0).image _
    obtain ⟨gr, hgr_mem, hgr_eq⟩ := Nat.sSup_mem h_ne_g h_fin_g.bddAbove
    dsimp only at hgr_eq
    obtain ⟨hr, hhr_mem, hge_gr_hr⟩ := ((misereGE_lde_iff hg hh).mp hge).2 gr hgr_mem
    have hih := flexibility_le_of_ge (hg.of_mem_rightMoves hgr_mem)
      (hh.of_mem_rightMoves hhr_mem) hge_gr_hr
    have h_le_h := flexibility_succ_le_of_mem_rightMoves hh hhi hhr_mem
    rw [flexibility_of_not_isInteger hgi, ← hgr_eq]
    omega
termination_by g
decreasing_by form_wf

theorem flexibility_eq_of_misereEQ {g h : GameForm} (hg : IsLde g) (hh : IsLde h)
    (heq : g ≡ₗ h) : flexibility g = flexibility h :=
  le_antisymm (flexibility_le_of_ge hg hh (misereGE_of_misereEQ heq))
    (flexibility_le_of_ge hh hg (misereGE_of_misereEQ heq.symm))

/--
If $G$ is a Left dead end, then we say a run $(G_0, G_1, \ldots, G_n)$ of $G$ of length
$n > 0$ is *flexible* if $G_i$ is not an integer for $i < n$. We define all runs of length
$0$ to be flexible.

This is [Davies (Definition 5.6 on p. 25)][davies:FactorisationsLeftDead:2024].
-/
@[expose] def IsFlexibleRun (l : List GameForm) : Prop :=
  IsRun l ∧ ∀ x ∈ l.dropLast, ¬ IsInteger x

/--
A flexible run is *maximal* if it ends at an integer; that is, if it cannot be extended to
a longer flexible run.

This is [Davies (Definition 5.6 on p. 25)][davies:FactorisationsLeftDead:2024].
-/
@[expose] def IsMaximalFlexibleRun (l : List GameForm) : Prop :=
  IsFlexibleRun l ∧ ∀ x ∈ l.getLast?, IsInteger x

theorem length_le_flexibility_of_isFlexibleRun {g : GameForm} (hg : IsLde g)
    {l : List GameForm} (hl : IsFlexibleRun (g :: l)) : l.length ≤ flexibility g := by
  induction l generalizing g with
  | nil => exact Nat.zero_le _
  | cons b l ih =>
    obtain ⟨⟨hb_mem, hb_run⟩, hnint⟩ := hl
    have hgi : ¬ IsInteger g := hnint g (by simp)
    have hb_flex : IsFlexibleRun (b :: l) :=
      ⟨hb_run, fun x hx => hnint x (by simp only [List.dropLast_cons₂]; exact List.mem_cons_of_mem _ hx)⟩
    have hih := ih (hg.of_mem_rightMoves hb_mem) hb_flex
    have h_le := flexibility_succ_le_of_mem_rightMoves hg hgi hb_mem
    simp only [List.length_cons]
    omega

theorem exists_isMaximalFlexibleRun_length_eq {g : GameForm} (hg : IsLde g) :
    ∃ l : List GameForm, IsMaximalFlexibleRun (g :: l) ∧ l.length = flexibility g := by
  by_cases hgi : IsInteger g
  · exact ⟨[], ⟨⟨trivial, by simp⟩, by simpa using hgi⟩, by simp [flexibility_of_isInteger hgi]⟩
  · have hg0 : g ≠ 0 := fun hc => hgi (hc ▸ ⟨0, by simp⟩)
    obtain ⟨gr, hgr⟩ := exists_isVersatileOption hg hg0
    obtain ⟨l, ⟨⟨hl_run, hl_nint⟩, hl_last⟩, hl_len⟩ :=
      exists_isMaximalFlexibleRun_length_eq (hg.of_mem_rightMoves hgr.1)
    refine ⟨gr :: l, ⟨⟨⟨hgr.1, hl_run⟩, fun x hx => ?_⟩, fun x hx => ?_⟩, ?_⟩
    · rw [List.dropLast_cons₂] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hgi
      · exact hl_nint x hx'
    · exact hl_last x (by rwa [List.getLast?_cons_cons] at hx)
    · rw [List.length_cons, hl_len, flexibility_eq_of_isVersatileOption hg hgi hgr]
termination_by g
decreasing_by exact Moves.Subposition.of_mem_moves hgr.1

/--
If $G$ is a Left dead end, then $f(G)$ is equal to the length of a longest flexible run of
$G$.

This is [Davies (Lemma 5.7 on p. 25)][davies:FactorisationsLeftDead:2024].
-/
theorem flexibility_eq_sSup_flexibleRun_length {g : GameForm} (hg : IsLde g) :
    flexibility g = sSup {n | ∃ l : List GameForm, IsFlexibleRun (g :: l) ∧ l.length = n} := by
  have hbdd : BddAbove {n | ∃ l : List GameForm, IsFlexibleRun (g :: l) ∧ l.length = n} :=
    ⟨flexibility g, fun n ⟨l, hl, hn⟩ => hn ▸ length_le_flexibility_of_isFlexibleRun hg hl⟩
  obtain ⟨l, hl, hl_len⟩ := exists_isMaximalFlexibleRun_length_eq hg
  exact le_antisymm (hl_len ▸ le_csSup hbdd ⟨l, hl.1, rfl⟩)
    (csSup_le ⟨l.length, l, hl.1, rfl⟩ fun n ⟨m, hm, hn⟩ =>
      hn ▸ length_le_flexibility_of_isFlexibleRun hg hm)

/--
If $G$ is a Left dead end, then we define a *racing option* of $G$ to be an option $G'$
such that $r(G') = r(G) - 1$.

This is [Davies (Definition 5.8 on p. 25)][davies:FactorisationsLeftDead:2024].
-/
@[expose] def IsRacingOption (gr g : GameForm) : Prop :=
  gr ∈ moves .right g ∧ race g = race gr + 1

/--
If $G$ is a Left dead end, then we define a *stalling option* of $G$ to be an option $G'$
such that $b(G') = b(G) - 1$.

This is [Davies (Definition 5.9 on p. 25)][davies:FactorisationsLeftDead:2024].
-/
@[expose] def IsStallingOption (gr g : GameForm) : Prop :=
  gr ∈ moves .right g ∧ birthday g = birthday gr + 1

theorem exists_isRacingOption {g : GameForm} (hg : IsLde g) (hg0 : g ≠ 0) :
    ∃ gr, IsRacingOption gr g :=
  exists_mem_rightMoves_race_succ hg hg0

theorem exists_isStallingOption {g : GameForm} (hg : IsLde g) (hg0 : g ≠ 0) :
    ∃ gr, IsStallingOption gr g :=
  exists_mem_rightMoves_birthday_succ hg hg0

theorem flexibility_singletonRight {x : GameForm} (hx : IsLde x) (hxi : ¬ IsInteger x) :
    flexibility !{(∅ : Set GameForm) | {x}} = flexibility x + 1 := by
  have hS := isLde_singletonRight hx
  have hSi : ¬ IsInteger !{(∅ : Set GameForm) | {x}} := by
    rw [← isInteger_iff_of_misereEQ ((isLde_neg_one).add hx) hS (neg_one_add_eq_singleton hx),
      show -(1 : GameForm) + x = x + -(1 : GameForm) from add_comm _ _,
      ← Nat.cast_one (R := GameForm), isInteger_add_neg_intCast_iff hx]
    exact hxi
  rw [flexibility_of_not_isInteger hSi, rightMoves_singletonRight, Set.image_singleton,
    csSup_singleton]
  omega

/--
If $G$ is a non-integer Left dead end, then $f(G + \overline{n}) = f(G) + n$ for all
$n \ge 0$.

This is [Davies (Proposition 5.10(1) on p. 26)][davies:FactorisationsLeftDead:2024].
-/
theorem flexibility_add_neg_intCast {g : GameForm} (hg : IsLde g) (hgi : ¬ IsInteger g) (n : ℕ) :
    flexibility (g + -(n : GameForm)) = flexibility g + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hgn : IsLde (g + -(n : GameForm)) := hg.add (isLde_neg_intCast n)
    have hgni : ¬ IsInteger (g + -(n : GameForm)) := by
      rw [isInteger_add_neg_intCast_iff hg]; exact hgi
    have hrw : g + -((n + 1 : ℕ) : GameForm) = -(1 : GameForm) + (g + -(n : GameForm)) := by
      rw [neg_intCast_add, Nat.cast_one]; ac_rfl
    rw [hrw, flexibility_eq_of_misereEQ ((isLde_neg_one).add hgn) (isLde_singletonRight hgn)
      (neg_one_add_eq_singleton hgn), flexibility_singletonRight hgn hgni, ih]
    omega

/-- See `flexibility_add_neg_intCast`. -/
theorem flexibility_neg_intCast_add {h : GameForm} (hh : IsLde h) (hhi : ¬ IsInteger h) (n : ℕ) :
    flexibility (-(n : GameForm) + h) = flexibility h + n := by
  rw [add_comm, flexibility_add_neg_intCast hh hhi]

/--
If $G$ and $H$ are non-integer Left dead ends, then
$f(G + H) = \max(b(G) + f(H), f(G) + b(H))$.

This is [Davies (Proposition 5.10(2) on p. 26)][davies:FactorisationsLeftDead:2024].
-/
theorem flexibility_add {g h : GameForm} (hg : IsLde g) (hh : IsLde h)
    (hgi : ¬ IsInteger g) (hhi : ¬ IsInteger h) :
    (flexibility (g + h) : NatOrdinal) =
      max (birthday g + flexibility h) (flexibility g + birthday h) := by
  have hg0 : g ≠ 0 := fun hc => hgi (hc ▸ ⟨0, by simp⟩)
  have hh0 : h ≠ 0 := fun hc => hhi (hc ▸ ⟨0, by simp⟩)
  have hgh : IsLde (g + h) := hg.add hh
  have hghi : ¬ IsInteger (g + h) := not_isInteger_add_of_not_isInteger_right hg hh hhi
  -- Upper bound: every Right option `x` of `g + h` has `f(x) + 1 ≤ M`.
  have hup : ∀ x ∈ moves .right (g + h), (flexibility x : NatOrdinal) + 1 ≤
      max (birthday g + flexibility h) (flexibility g + birthday h) := by
    intro x hx
    rw [moves_add] at hx
    rcases hx with ⟨gr, hgr, rfl⟩ | ⟨hr, hhr, rfl⟩
    · have hb := Order.add_one_le_of_lt (birthday_lt_of_mem_moves hgr)
      by_cases hgri : IsInteger gr
      · obtain ⟨m, rfl⟩ := exists_eq_neg_intCast_of_isInteger (hg.of_mem_rightMoves hgr) hgri
        rw [birthday_neg, birthday_natCast] at hb
        rw [flexibility_neg_intCast_add hh hhi m, Nat.cast_add, add_assoc, add_comm (birthday g)]
        exact le_max_of_le_left (add_le_add_right hb _)
      · have hf := flexibility_succ_le_of_mem_rightMoves hg hgi hgr
        rw [flexibility_add (hg.of_mem_rightMoves hgr) hh hgri hhi, ← max_add_add_right]
        refine max_le_max ?_ ?_
        · rw [add_right_comm]
          exact add_le_add_left hb _
        · rw [add_right_comm]
          exact add_le_add_left (by exact_mod_cast hf) _
    · have hb := Order.add_one_le_of_lt (birthday_lt_of_mem_moves hhr)
      by_cases hhri : IsInteger hr
      · obtain ⟨m, rfl⟩ := exists_eq_neg_intCast_of_isInteger (hh.of_mem_rightMoves hhr) hhri
        rw [birthday_neg, birthday_natCast] at hb
        rw [flexibility_add_neg_intCast hg hgi m, Nat.cast_add, add_assoc]
        exact le_max_of_le_right (add_le_add_right hb _)
      · have hf := flexibility_succ_le_of_mem_rightMoves hh hhi hhr
        rw [flexibility_add hg (hh.of_mem_rightMoves hhr) hgi hhri, ← max_add_add_right]
        refine max_le_max ?_ ?_
        · rw [add_assoc]
          exact add_le_add_right (by exact_mod_cast hf) _
        · rw [add_assoc]
          exact add_le_add_right hb _
  -- Lower bound: some Right option `x` of `g + h` has `M ≤ f(x) + 1`.
  have hlow : ∃ x ∈ moves .right (g + h),
      max (birthday g + flexibility h) (flexibility g + birthday h) ≤
        (flexibility x : NatOrdinal) + 1 := by
    rcases le_total ((flexibility g : NatOrdinal) + birthday h)
      (birthday g + flexibility h) with hle | hle
    · obtain ⟨gr, hgr, hbr⟩ := exists_mem_rightMoves_birthday_succ hg hg0
      refine ⟨gr + h, by rw [moves_add]; exact Or.inl ⟨gr, hgr, rfl⟩, ?_⟩
      rw [max_eq_left hle, hbr, add_right_comm]
      by_cases hgri : IsInteger gr
      · obtain ⟨m, rfl⟩ := exists_eq_neg_intCast_of_isInteger (hg.of_mem_rightMoves hgr) hgri
        rw [birthday_neg, birthday_natCast, flexibility_neg_intCast_add hh hhi m, Nat.cast_add,
          add_comm (m : NatOrdinal)]
      · rw [flexibility_add (hg.of_mem_rightMoves hgr) hh hgri hhi]
        exact add_le_add_left (le_max_left _ _) _
    · obtain ⟨hr, hhr, hbr⟩ := exists_mem_rightMoves_birthday_succ hh hh0
      refine ⟨g + hr, by rw [moves_add]; exact Or.inr ⟨hr, hhr, rfl⟩, ?_⟩
      rw [max_eq_right hle, hbr, ← add_assoc]
      by_cases hhri : IsInteger hr
      · obtain ⟨m, rfl⟩ := exists_eq_neg_intCast_of_isInteger (hh.of_mem_rightMoves hhr) hhri
        rw [birthday_neg, birthday_natCast, flexibility_add_neg_intCast hg hgi m, Nat.cast_add]
      · rw [flexibility_add hg (hh.of_mem_rightMoves hhr) hgi hhri]
        exact add_le_add_left (le_max_right _ _) _
  have h_fin : ((fun x => flexibility x) '' moves .right (g + h)).Finite :=
    (IsShort.finite_moves .right hgh.short).image _
  have hgh0 : g + h ≠ 0 := fun hc => hghi (hc ▸ ⟨0, by simp⟩)
  have h_ne : ((fun x => flexibility x) '' moves .right (g + h)).Nonempty :=
    (hgh.rightMoves_nonempty hgh0).image _
  obtain ⟨y, hy_mem, hy_eq⟩ := Nat.sSup_mem h_ne h_fin.bddAbove
  dsimp only at hy_eq
  obtain ⟨x, hx_mem, hx_le⟩ := hlow
  have hx_sSup : flexibility x ≤ sSup ((fun x => flexibility x) '' moves .right (g + h)) :=
    le_csSup h_fin.bddAbove (Set.mem_image_of_mem _ hx_mem)
  rw [flexibility_of_not_isInteger hghi, ← hy_eq, add_comm 1, Nat.cast_add, Nat.cast_one]
  exact le_antisymm (hup y hy_mem)
    (hx_le.trans (add_le_add_left (Nat.cast_le.mpr (hx_sSup.trans hy_eq.ge)) 1))
termination_by (g, h)
decreasing_by all_goals form_wf

/--
If $G$, $H$, and $K$ are Left dead ends such that $H$ is non-zero, $K$ is not an integer,
and $H + K \ge G$, then $b(H) < f(G)$.

This is [Davies (Proposition 5.11 on p. 27)][davies:FactorisationsLeftDead:2024].
-/
theorem birthday_lt_flexibility_of_ge {g h k : GameForm}
    (hg : IsLde g) (hh : IsLde h) (hk : IsLde k)
    (hh0 : h ≠ 0) (hk_ni : ¬ IsInteger k) (hge : (h + k) ≥ₗ g) :
    birthday h < (flexibility g : NatOrdinal) :=
  lt_of_lt_of_le (birthday_lt_flexibility_add_of_not_isInteger hh hk hh0 hk_ni)
    (Nat.cast_le.mpr (flexibility_le_of_ge (hh.add hk) hg hge))

theorem isInteger_neg_intCast (n : ℕ) : IsInteger (-(n : GameForm)) :=
  ⟨-(n : ℤ), by rw [← Form.intCast_nat n, ← Form.intCast_neg]⟩

theorem not_isInteger_of_multi_good {g h k : GameForm} (hg : IsLde g) (hh : IsLde h)
    (hk : IsLde k) (hk0 : k ≠ 0)
    (hmulti : ∃ a b, IsGoodOption a g ∧ IsGoodOption b g ∧ ¬ (a ≡ₗ b))
    (heq : g ≡ₗ (h + k)) : ¬ IsInteger k := by
  intro hki
  obtain ⟨n, rfl⟩ := exists_eq_neg_intCast_of_isInteger hk hki
  obtain ⟨j, rfl⟩ : ∃ j, n = 1 + j := by
    have hn : n ≠ 0 := fun hc => hk0 (by rw [hc]; simp)
    exact ⟨n - 1, by omega⟩
  have hrw : h + -((1 + j : ℕ) : GameForm) = -(1 : GameForm) + (h + -(j : GameForm)) := by
    rw [neg_intCast_add, Nat.cast_one]; ac_rfl
  have hsplit : g ≡ₗ (-(1 : GameForm) + (h + -(j : GameForm))) := by rw [← hrw]; exact heq
  obtain ⟨-, -, -, huniq⟩ := (unique_good_option_iff hg (hh.add (isLde_neg_intCast j))).mpr hsplit
  obtain ⟨a, b, ha, hb, hab⟩ := hmulti
  exact hab ((huniq a ha).trans (huniq b hb).symm)

/--
If $G$ is a Left dead end with more than one good option, then, for any non-zero Left dead
ends $H$ and $K$ with $H + K = G$, it holds that $b(H), b(K) < f(G)$.

This is [Davies (Corollary 5.12 on p. 28)][davies:FactorisationsLeftDead:2024].
-/
theorem birthday_lt_flexibility_of_multi_good {g h k : GameForm} (hg : IsLde g)
    (hh : IsLde h) (hk : IsLde k) (hh0 : h ≠ 0) (hk0 : k ≠ 0)
    (hmulti : ∃ a b, IsGoodOption a g ∧ IsGoodOption b g ∧ ¬ (a ≡ₗ b))
    (heq : g ≡ₗ (h + k)) :
    birthday h < (flexibility g : NatOrdinal) ∧ birthday k < (flexibility g : NatOrdinal) := by
  have heq' : (k + h) ≥ₗ g := by
    rw [add_comm]
    exact misereGE_of_misereEQ heq.symm
  have hk_ni := not_isInteger_of_multi_good hg hh hk hk0 hmulti heq
  have hh_ni : ¬ IsInteger h := by
    refine not_isInteger_of_multi_good hg hk hh hh0 hmulti ?_
    rw [add_comm]
    exact heq
  exact ⟨birthday_lt_flexibility_of_ge hg hh hk hh0 hk_ni (misereGE_of_misereEQ heq.symm),
    birthday_lt_flexibility_of_ge hg hk hh hk0 hh_ni heq'⟩

/--
If $G$ is a Left dead end with more than one good option, and $b(G) > 2 \cdot f(G) - 2$,
then $G$ is an atom.

This is [Davies (Corollary 5.13 on p. 28)][davies:FactorisationsLeftDead:2024].
-/
theorem atom_of_birthday_gt {g : GameForm} (hg : IsLde g)
    (hmulti : ∃ a b, IsGoodOption a g ∧ IsGoodOption b g ∧ ¬ (a ≡ₗ b))
    (hb : (flexibility g : NatOrdinal) + (flexibility g : NatOrdinal) < birthday g + 2) :
    IsLdeAtom g := by
  obtain ⟨a, b, ha_good, hb_good, hab⟩ := hmulti
  refine ⟨hg, ?_, fun h k hh hk heq => ?_⟩
  · intro hc
    have hmem := ha_good.1
    rw [hc, moves_zero] at hmem
    exact Set.notMem_empty _ hmem
  · by_contra hcon
    push_neg at hcon
    obtain ⟨hbh, hbk⟩ := birthday_lt_flexibility_of_multi_good hg hh hk hcon.1 hcon.2
      ⟨a, b, ha_good, hb_good, hab⟩ heq
    have hb_eq : birthday g = birthday h + birthday k := by
      rw [birthday_eq_of_misereEQ hg (hh.add hk) heq, birthday_add]
    refine absurd hb (not_lt.mpr ?_)
    rw [hb_eq]
    calc birthday h + birthday k + 2 = (birthday h + 1) + (birthday k + 1) := by
          rw [← one_add_one_eq_two]
          ac_rfl
      _ ≤ (flexibility g : NatOrdinal) + (flexibility g : NatOrdinal) :=
          add_le_add (Order.add_one_le_of_lt hbh) (Order.add_one_le_of_lt hbk)

/--
If $G$ is a Left dead end with $f(G) = 1$, then $G$ is an atom.

This is [Davies (Proposition 5.14 on p. 28)][davies:FactorisationsLeftDead:2024].
-/
theorem atom_of_flexibility_one {g : GameForm} (hg : IsLde g) (hf : flexibility g = 1) :
    IsLdeAtom g := by
  have hgi : ¬ IsInteger g := by
    intro hc
    rw [flexibility_of_isInteger hc] at hf
    exact absurd hf (by omega)
  have hg0 : g ≠ 0 := fun hc => hgi (hc ▸ ⟨0, by simp⟩)
  have hmulti : ∃ a b, IsGoodOption a g ∧ IsGoodOption b g ∧ ¬ (a ≡ₗ b) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨w₀, hw₀⟩ := hg.rightMoves_nonempty hg0
    obtain ⟨w, hw_good, -⟩ := exists_isGoodOption_le_of_mem_rightMoves hg hw₀
    obtain ⟨m, rfl⟩ := exists_eq_neg_intCast_of_isInteger (hg.of_mem_rightMoves hw_good.1)
      (isInteger_of_mem_rightMoves_of_flexibility_le_one hg hgi hf.le hw_good.1)
    have hgeq : g ≡ₗ -((1 + m : ℕ) : GameForm) := by
      rw [neg_intCast_add, Nat.cast_one]
      exact (unique_good_option_iff hg (isLde_neg_intCast m)).mp
        ⟨-(m : GameForm), hw_good, fun _ _ => rfl, fun y hy => hcon y (-(m : GameForm)) hy hw_good⟩
    have hfeq := flexibility_eq_of_misereEQ hg (isLde_neg_intCast (1 + m)) hgeq
    rw [flexibility_of_isInteger (isInteger_neg_intCast (1 + m))] at hfeq
    omega
  refine atom_of_birthday_gt hg hmulti ?_
  rw [hf, Nat.cast_one, show (1 : NatOrdinal) + 1 = 0 + 2 from by
    rw [zero_add]; exact one_add_one_eq_two]
  exact add_lt_add_left (birthday_pos_of_ne_zero hg hg0) 2

/--
If $G$ is a Left dead end with $f(G) = 2$, then either $G$ has exactly one good option
(i.e. $\overline{1} \mid G$), or $G$ is an atom.

This is [Davies (Proposition 5.14 on p. 28)][davies:FactorisationsLeftDead:2024].
-/
theorem atom_of_flexibility_two {g : GameForm} (hg : IsLde g) (hf : flexibility g = 2) :
    HasUniqueGoodOption g ∨ IsLdeAtom g := by
  have hgi : ¬ IsInteger g := by
    intro hc
    rw [flexibility_of_isInteger hc] at hf
    omega
  have hg0 : g ≠ 0 := fun hc => hgi (hc ▸ ⟨0, by simp⟩)
  rcases hasUniqueGoodOption_or_multi hg hg0 with huniq | hmulti
  · exact Or.inl huniq
  · refine Or.inr (atom_of_birthday_gt hg hmulti ?_)
    have h := flexibility_lt_birthday_of_ne_zero hg hg0
    rw [hf, Nat.cast_ofNat] at h ⊢
    exact add_lt_add_left h 2

theorem misereEQ_of_flexibility_le_one {g h : GameForm} (hg : IsLde g) (hh : IsLde h)
    (hfg : flexibility g ≤ 1) (hfh : flexibility h ≤ 1)
    (hT : terminalLengths g = terminalLengths h) : g ≡ₗ h :=
  MisereEq.of_antisymm (ge_of_flexibility_le_one hg hh hfg hT.subset)
    (ge_of_flexibility_le_one hh hg hfh hT.symm.subset)

theorem terminalLengths_of_birthday_two {g : GameForm} (hg : IsLde g)
    (hgi : ¬ IsInteger g) (hb : birthday g = 2) : terminalLengths g = {1, 2} := by
  have hg0 : g ≠ 0 := fun hc => hgi (hc ▸ ⟨0, by simp⟩)
  have hM : sSup (terminalLengths g) = 2 := by
    rw [birthday_eq_sSup_terminalLengths hg] at hb
    exact_mod_cast hb
  have hfin := terminalLengths_finite_nonempty hg
  have h1 : 1 ≤ race g :=
    Nat.one_le_iff_ne_zero.mpr fun hc => hg0 ((lde_race_zero_iff hg).mp hc)
  have h2 := race_lt_sSup_terminalLengths hg hgi
  rw [hM] at h2
  have hr1 : race g = 1 := by omega
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro ht
    have hlo : race g ≤ t := Nat.sInf_le ht
    have hhi : t ≤ sSup (terminalLengths g) := le_csSup hfin.1.bddAbove ht
    rw [hM] at hhi
    omega
  · rintro (rfl | rfl)
    · exact hr1 ▸ Nat.sInf_mem hfin.2
    · exact hM ▸ Nat.sSup_mem hfin.2 hfin.1.bddAbove

theorem terminalLengths_waitingGame_one : terminalLengths (waitingGame 1) = {1} := by
  rw [terminalLengths_of_ne_zero (waitingGame_succ_ne_zero 0),
    rightMoves_waitingGame]
  simp [waitingGame, terminalLengths_zero]

theorem terminalLengths_waitingGame_two : terminalLengths (waitingGame 2) = {1, 2} := by
  rw [terminalLengths_of_ne_zero (waitingGame_succ_ne_zero 1),
    rightMoves_waitingGame]
  rw [Set.biUnion_insert, Set.biUnion_singleton, terminalLengths_zero,
    terminalLengths_waitingGame_one, Set.image_singleton, Set.image_singleton,
    Set.singleton_union]

theorem birthday_waitingGame_two : birthday (waitingGame 2) = 2 := by
  rw [birthday_eq_sSup_terminalLengths (isLde_waitingGame 2), terminalLengths_waitingGame_two,
    csSup_pair, show max 1 2 = 2 by omega, Nat.cast_ofNat]

theorem not_isInteger_waitingGame_two : ¬ IsInteger (waitingGame 2) := by
  intro hc
  have h := (isInteger_iff_terminalLengths_subsingleton (isLde_waitingGame 2)).mp hc
  rw [terminalLengths_waitingGame_two] at h
  have := h (Set.mem_insert 1 {2}) (Set.mem_insert_of_mem 1 rfl)
  omega

private theorem flexibility_le_one_of_birthday_two {g : GameForm} (hg : IsLde g)
    (hgi : ¬ IsInteger g) (hb : birthday g = 2) : flexibility g ≤ 1 := by
  have hg0 : g ≠ 0 := fun hc => hgi (hc ▸ ⟨0, by simp⟩)
  have h := flexibility_lt_birthday_of_ne_zero hg hg0
  rw [hb] at h
  have : flexibility g < 2 := by exact_mod_cast h
  omega

theorem eq_neg_two_or_misereEQ_waitingGame_two {g : GameForm} (hg : IsLde g)
    (hb : birthday g = 2) : g = -(2 : GameForm) ∨ (g ≡ₗ waitingGame 2) := by
  by_cases hgi : IsInteger g
  · obtain ⟨n, rfl⟩ := exists_eq_neg_intCast_of_isInteger hg hgi
    rw [birthday_neg, birthday_natCast] at hb
    have hn : n = 2 := by exact_mod_cast hb
    exact Or.inl (by rw [hn, Nat.cast_ofNat])
  · refine Or.inr (misereEQ_of_flexibility_le_one hg (isLde_waitingGame 2)
      (flexibility_le_one_of_birthday_two hg hgi hb)
      (flexibility_le_one_of_birthday_two (isLde_waitingGame 2) not_isInteger_waitingGame_two
        birthday_waitingGame_two) ?_)
    rw [terminalLengths_of_birthday_two hg hgi hb, terminalLengths_waitingGame_two]

/--
If $G$ is a Left dead end with $f(G) = 3$, then either $G$ has exactly one good option,
$G = 2 \cdot W_2$, or $G$ is an atom.

This is [Davies (Proposition 5.14 on p. 28)][davies:FactorisationsLeftDead:2024].
-/
theorem atom_of_flexibility_three {g : GameForm} (hg : IsLde g) (hf : flexibility g = 3) :
    HasUniqueGoodOption g ∨ (g ≡ₗ 2 • waitingGame 2) ∨ IsLdeAtom g := by
  have hgi : ¬ IsInteger g := by
    intro hc
    rw [flexibility_of_isInteger hc] at hf
    omega
  have hg0 : g ≠ 0 := fun hc => hgi (hc ▸ ⟨0, by simp⟩)
  rcases hasUniqueGoodOption_or_multi hg hg0 with huniq | hmulti
  · exact Or.inl huniq
  refine Or.inr ?_
  by_cases hatom : IsLdeAtom g
  · exact Or.inr hatom
  refine Or.inl ?_
  obtain ⟨h, k, hh, hk, heq, hh0, hk0⟩ :
      ∃ h k, IsLde h ∧ IsLde k ∧ (g ≡ₗ (h + k)) ∧ h ≠ 0 ∧ k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hatom ⟨hg, hg0, fun h k hh hk hsplit => by
      by_contra hne
      push_neg at hne
      exact hne.2 (hc h k hh hk hsplit hne.1)⟩
  have heq' : g ≡ₗ (k + h) := by rw [add_comm]; exact heq
  have hh_ni : ¬ IsInteger h := not_isInteger_of_multi_good hg hk hh hh0 hmulti heq'
  have hk_ni : ¬ IsInteger k := not_isInteger_of_multi_good hg hh hk hk0 hmulti heq
  obtain ⟨hbh, hbk⟩ := birthday_lt_flexibility_of_multi_good hg hh hk hh0 hk0 hmulti heq
  rw [hf, birthday_eq_sSup_terminalLengths hh] at hbh
  rw [hf, birthday_eq_sSup_terminalLengths hk] at hbk
  have hbh' : birthday h = 2 := by
    have h1 : sSup (terminalLengths h) < 3 := by exact_mod_cast hbh
    have h2 := two_le_sSup_terminalLengths hh hh0 hh_ni
    rw [birthday_eq_sSup_terminalLengths hh, show sSup (terminalLengths h) = 2 by omega,
      Nat.cast_ofNat]
  have hbk' : birthday k = 2 := by
    have h1 : sSup (terminalLengths k) < 3 := by exact_mod_cast hbk
    have h2 := two_le_sSup_terminalLengths hk hk0 hk_ni
    rw [birthday_eq_sSup_terminalLengths hk, show sSup (terminalLengths k) = 2 by omega,
      Nat.cast_ofNat]
  have hhW : h ≡ₗ waitingGame 2 := by
    rcases eq_neg_two_or_misereEQ_waitingGame_two hh hbh' with rfl | hW
    · exact absurd (isInteger_neg_intCast 2) hh_ni
    · exact hW
  have hkW : k ≡ₗ waitingGame 2 := by
    rcases eq_neg_two_or_misereEQ_waitingGame_two hk hbk' with rfl | hW
    · exact absurd (isInteger_neg_intCast 2) hk_ni
    · exact hW
  rw [two_nsmul]
  exact heq.trans (Form.MisereQuotient.add_misereEQ_add hk.shortDeadEnding
    (isLde_waitingGame 2).shortDeadEnding hhW hkW)

/-! ## Lengths of factorisations -/

/-- $\overline{\mathsf{L}(G)}$, the length of a longest factorisation of $G$, with
$\overline{\mathsf{L}(0)} = 0$. -/
@[expose] def longestFactorisationLen (g : GameForm) : ℕ :=
  sSup {n | ∃ s : Multiset GameForm, IsFactorisation s g ∧ Multiset.card s = n}

theorem bddAbove_factorisationLen {g : GameForm} (hg : IsLde g) :
    BddAbove {n | ∃ s : Multiset GameForm, IsFactorisation s g ∧ Multiset.card s = n} :=
  ⟨race g, fun _ ⟨_, hs, hn⟩ => hn ▸ factorisation_length_le_race hg hs⟩

theorem card_le_longestFactorisationLen {g : GameForm} (hg : IsLde g)
    {s : Multiset GameForm} (hs : IsFactorisation s g) :
    Multiset.card s ≤ longestFactorisationLen g :=
  le_csSup (bddAbove_factorisationLen hg) ⟨s, hs, rfl⟩

theorem exists_isFactorisation_card_longestFactorisationLen {g : GameForm} (hg : IsLde g) :
    ∃ s : Multiset GameForm, IsFactorisation s g ∧ Multiset.card s = longestFactorisationLen g := by
  obtain ⟨s, hs⟩ := lde_atomic hg
  have h_ne : {n | ∃ s : Multiset GameForm, IsFactorisation s g ∧ Multiset.card s = n}.Nonempty :=
    ⟨Multiset.card s, s, hs, rfl⟩
  exact Nat.sSup_mem h_ne (bddAbove_factorisationLen hg)

theorem longestFactorisationLen_eq_of_misereEQ {g h : GameForm} (heq : g ≡ₗ h) :
    longestFactorisationLen g = longestFactorisationLen h := by
  unfold longestFactorisationLen
  congr 1
  ext n
  constructor
  · rintro ⟨s, ⟨hatoms, hsum⟩, rfl⟩
    exact ⟨s, ⟨hatoms, hsum.trans heq⟩, rfl⟩
  · rintro ⟨s, ⟨hatoms, hsum⟩, rfl⟩
    exact ⟨s, ⟨hatoms, hsum.trans heq.symm⟩, rfl⟩

theorem exists_eq_add_sum_of_mem_rightMoves_sum {s : Multiset GameForm} {x : GameForm}
    (hx : x ∈ moves .right s.sum) :
    ∃ a t, s = a ::ₘ t ∧ ∃ ar ∈ moves .right a, x = ar + t.sum := by
  revert x
  induction s using Multiset.induction with
  | empty =>
    intro x hx
    rw [Multiset.sum_zero, moves_zero] at hx
    exact absurd hx (Set.notMem_empty _)
  | cons a t ih =>
    intro x hx
    rw [Multiset.sum_cons, moves_add] at hx
    simp only [Set.mem_union, Set.mem_image] at hx
    rcases hx with ⟨ar, har, rfl⟩ | ⟨y, hy, rfl⟩
    · exact ⟨a, t, rfl, ar, har, rfl⟩
    · obtain ⟨b, u, rfl, br, hbr, rfl⟩ := ih hy
      exact ⟨b, a ::ₘ u, Multiset.cons_swap a b u, br, hbr, by rw [Multiset.sum_cons]; ac_rfl⟩

/--
If $G$ is a Left dead end, then $\overline{\mathsf{L}(G)} \le \overline{\mathsf{L}(G')} + 1$
for every good option $G'$ of $G$.

This is [Davies (Lemma 6.1 on p. 30)][davies:FactorisationsLeftDead:2024].
-/
theorem longestLen_le_good_option {g gr : GameForm} (hg : IsLde g) (hgr : IsGoodOption gr g) :
    longestFactorisationLen g ≤ longestFactorisationLen gr + 1 := by
  obtain ⟨s, hs, hcard⟩ := exists_isFactorisation_card_longestFactorisationLen hg
  have hs_lde : ∀ a ∈ s, IsLde a := fun a ha => (hs.1 a ha).1
  have hsum_lde : IsLde s.sum := isLde_sum hs_lde
  obtain ⟨y, hy_good, hy_eq⟩ :=
    lde_good_option_misereEQ hg hsum_lde hs.2.symm hgr
  obtain ⟨a, t, rfl, ar, har, rfl⟩ := exists_eq_add_sum_of_mem_rightMoves_sum hy_good.1
  have ha_lde : IsLde a := hs_lde a (Multiset.mem_cons_self a t)
  have ht_lde : ∀ b ∈ t, IsLde b := fun b hb => hs_lde b (Multiset.mem_cons_of_mem hb)
  have har_lde : IsLde ar := ha_lde.of_mem_rightMoves har
  obtain ⟨u, hu⟩ := lde_atomic har_lde
  have hut : IsFactorisation (u + t) (ar + t.sum) := by
    refine ⟨fun b hb => ?_, ?_⟩
    · rcases Multiset.mem_add.mp hb with hb' | hb'
      · exact hu.1 b hb'
      · exact hs.1 b (Multiset.mem_cons_of_mem hb')
    · rw [Multiset.sum_add]
      exact Form.MisereQuotient.add_misereEQ_add (isLde_sum ht_lde).shortDeadEnding
        har_lde.shortDeadEnding hu.2 (fun _ _ => rfl)
  have hle : Multiset.card t ≤ longestFactorisationLen (ar + t.sum) := by
    refine le_trans ?_ (card_le_longestFactorisationLen (har_lde.add (isLde_sum ht_lde)) hut)
    rw [Multiset.card_add]
    omega
  rw [longestFactorisationLen_eq_of_misereEQ hy_eq]
  rw [Multiset.card_cons] at hcard
  omega

theorem isLdeAtom_neg_one : IsLdeAtom (-(1 : GameForm)) :=
  lde_atom_of_race_one isLde_neg_one
    (by rw [race, ← Nat.cast_one (R := GameForm), terminalLengths_neg_intCast]
        exact csInf_singleton 1)

/--
If $G$ is a Left dead end with exactly one good option $G'$, then
$\overline{\mathsf{L}(G)} = \overline{\mathsf{L}(G')} + 1$.

This is [Davies (Theorem 6.2 on p. 30)][davies:FactorisationsLeftDead:2024].
-/
theorem longestLen_of_unique_good {g gr : GameForm} (hg : IsLde g) (hgr : IsLde gr)
    (hgood : IsGoodOption gr g) (huniq : ∀ gr', IsGoodOption gr' g → gr' ≡ₗ gr) :
    longestFactorisationLen g = longestFactorisationLen gr + 1 := by
  refine le_antisymm (longestLen_le_good_option hg hgood) ?_
  have hsplit : g ≡ₗ (-(1 : GameForm) + gr) :=
    (unique_good_option_iff hg hgr).mp ⟨gr, hgood, fun _ _ => rfl, huniq⟩
  obtain ⟨u, hu, hu_card⟩ := exists_isFactorisation_card_longestFactorisationLen hgr
  have hfac : IsFactorisation (-(1 : GameForm) ::ₘ u) g := by
    refine ⟨fun b hb => ?_, ?_⟩
    · rcases Multiset.mem_cons.mp hb with rfl | hb'
      · exact isLdeAtom_neg_one
      · exact hu.1 b hb'
    · rw [Multiset.sum_cons]
      exact (Form.MisereQuotient.add_misereEQ_add
        (isLde_sum fun b hb => (hu.1 b hb).1).shortDeadEnding
        (isLde_neg_one).shortDeadEnding (fun _ _ => rfl) hu.2).trans hsplit.symm
  have := card_le_longestFactorisationLen hg hfac
  rw [Multiset.card_cons, hu_card] at this
  exact this

private theorem not_isInteger_of_mem_isFactorisation {g : GameForm} (hg : IsLde g)
    (hmulti : ∃ a b, IsGoodOption a g ∧ IsGoodOption b g ∧ ¬ (a ≡ₗ b))
    {s : Multiset GameForm} (hs : IsFactorisation s g) {b : GameForm} (hb : b ∈ s) :
    ¬ IsInteger b := by
  obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hb
  have hb_atom := hs.1 b (Multiset.mem_cons_self b u)
  have hsum := hs.2
  rw [Multiset.sum_cons, add_comm] at hsum
  exact not_isInteger_of_multi_good hg
    (isLde_sum fun c hc => (hs.1 c (Multiset.mem_cons_of_mem hc)).1) hb_atom.1 hb_atom.2.1
    hmulti hsum.symm

private theorem card_lt_ncard_terminalLengths_sum {s : Multiset GameForm}
    (hs : ∀ a ∈ s, IsLde a) (hsi : ∀ a ∈ s, ¬ IsInteger a) :
    Multiset.card s < (terminalLengths s.sum).ncard := by
  induction s using Multiset.induction with
  | empty => simp [terminalLengths_zero]
  | cons a t ih =>
    have h1 := ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))
      (fun b hb => hsi b (Multiset.mem_cons_of_mem hb))
    have h2 := ncard_lt_ncard_terminalLengths_add (hs a (Multiset.mem_cons_self a t))
      (isLde_sum fun b hb => hs b (Multiset.mem_cons_of_mem hb))
      (hsi a (Multiset.mem_cons_self a t))
    rw [Multiset.sum_cons, Multiset.card_cons]
    omega

private theorem two_mul_card_le_birthday_sum {s : Multiset GameForm}
    (hs : ∀ a ∈ s, IsLde a) (hs0 : ∀ a ∈ s, a ≠ 0) (hsi : ∀ a ∈ s, ¬ IsInteger a) :
    ((2 * Multiset.card s : ℕ) : NatOrdinal) ≤ birthday s.sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    have ha_lde := hs a (Multiset.mem_cons_self a t)
    have ht_lde : ∀ b ∈ t, IsLde b := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    have h1 := ih ht_lde (fun b hb => hs0 b (Multiset.mem_cons_of_mem hb))
      (fun b hb => hsi b (Multiset.mem_cons_of_mem hb))
    have h2 := two_le_sSup_terminalLengths ha_lde (hs0 a (Multiset.mem_cons_self a t))
      (hsi a (Multiset.mem_cons_self a t))
    rw [Multiset.sum_cons, Multiset.card_cons, birthday_add,
      birthday_eq_sSup_terminalLengths ha_lde,
      show 2 * (Multiset.card t + 1) = 2 + 2 * Multiset.card t by omega, Nat.cast_add]
    exact add_le_add (by exact_mod_cast h2) h1

/--
If $G$ is a Left dead end with more than one good option, then
$$\overline{\mathsf{L}(G)} \le \min\left\{r(G),\ \overline{\mathsf{L}(G')} + 1,\ |T(G)| - 1,\
\frac{f(G) + 1}{2}\right\},$$
where $G'$ ranges over all good options of $G$.

This is [Davies (Theorem 6.3 on p. 30)][davies:FactorisationsLeftDead:2024].
-/
theorem longestLen_bound {g : GameForm} (hg : IsLde g)
    (hmulti : ∃ a b, IsGoodOption a g ∧ IsGoodOption b g ∧ ¬ (a ≡ₗ b)) :
    longestFactorisationLen g ≤ race g ∧
      (∀ gr, IsGoodOption gr g → longestFactorisationLen g ≤ longestFactorisationLen gr + 1) ∧
      longestFactorisationLen g + 1 ≤ (terminalLengths g).ncard ∧
      2 * longestFactorisationLen g ≤ flexibility g + 1 := by
  obtain ⟨s, hs, hcard⟩ := exists_isFactorisation_card_longestFactorisationLen hg
  have hs_lde : ∀ a ∈ s, IsLde a := fun a ha => (hs.1 a ha).1
  have hs0 : ∀ a ∈ s, a ≠ 0 := fun a ha => (hs.1 a ha).2.1
  have hs_ni : ∀ a ∈ s, ¬ IsInteger a := fun a ha =>
    not_isInteger_of_mem_isFactorisation hg hmulti hs ha
  have hg0 : g ≠ 0 := by
    obtain ⟨a, -, ha, -, -⟩ := hmulti
    intro hc
    have hmem := ha.1
    rw [hc, moves_zero] at hmem
    exact Set.notMem_empty a hmem
  have hgi : ¬ IsInteger g :=
    not_isInteger_of_multi_good hg isLde_zero hg hg0 hmulti
      (by rw [zero_add]; exact fun _ _ => rfl)
  have hf1 : 1 ≤ flexibility g := by
    rw [flexibility_of_not_isInteger hgi]
    omega
  refine ⟨hcard ▸ factorisation_length_le_race hg hs, fun gr hgr =>
    longestLen_le_good_option hg hgr, ?_, ?_⟩
  · have h := card_lt_ncard_terminalLengths_sum hs_lde hs_ni
    rw [terminalLengths_eq_of_misereEQ (isLde_sum hs_lde) hg hs.2] at h
    omega
  · rcases Nat.lt_or_ge (Multiset.card s) 2 with hk | hk
    · omega
    obtain ⟨a, t, rfl⟩ : ∃ a t, s = a ::ₘ t := by
      have hne : s ≠ 0 := by
        intro hc
        rw [hc, Multiset.card_zero] at hk
        omega
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
      obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
      exact ⟨a, t, ht⟩
    rw [Multiset.card_cons] at hcard hk
    have ha_lde := hs_lde a (Multiset.mem_cons_self a t)
    have ht_lde : ∀ b ∈ t, IsLde b := fun b hb => hs_lde b (Multiset.mem_cons_of_mem hb)
    have htsum_lde : IsLde t.sum := isLde_sum ht_lde
    have hbt := two_mul_card_le_birthday_sum ht_lde
      (fun b hb => hs0 b (Multiset.mem_cons_of_mem hb))
      (fun b hb => hs_ni b (Multiset.mem_cons_of_mem hb))
    have ht0 : t.sum ≠ 0 := by
      intro hc
      rw [hc, birthday_zero] at hbt
      have : 2 * Multiset.card t ≤ 0 := by exact_mod_cast hbt
      omega
    have hge : (t.sum + a) ≥ₗ g := by
      refine misereGE_of_misereEQ ?_
      rw [add_comm, ← Multiset.sum_cons]
      exact hs.2
    have h511 := birthday_lt_flexibility_of_ge hg htsum_lde ha_lde ht0
      (hs_ni a (Multiset.mem_cons_self a t)) hge
    have h511' : 2 * Multiset.card t < flexibility g := by exact_mod_cast hbt.trans_lt h511
    omega

private theorem card_pos_iff_of_isFactorisation {g : GameForm} (hg : IsLde g)
    {s : Multiset GameForm} (hs : IsFactorisation s g) : 0 < Multiset.card s ↔ g ≠ 0 := by
  have hs_lde : ∀ a ∈ s, IsLde a := fun a ha => (hs.1 a ha).1
  constructor
  · intro hpos hg0
    have := card_le_race_sum hs.1
    rw [race_eq_of_misereEQ (isLde_sum hs_lde) hg hs.2, hg0,
      (lde_race_zero_iff isLde_zero).mpr rfl] at this
    omega
  · intro hg0
    rcases Nat.eq_zero_or_pos (Multiset.card s) with hc | hc
    · rw [Multiset.card_eq_zero] at hc
      subst hc
      exact absurd ((lde_misereEQ_zero_iff hg).mp (show g ≡ₗ 0 by simpa using hs.2.symm)) hg0
    · exact hc

@[simp] theorem longestFactorisationLen_zero : longestFactorisationLen (0 : GameForm) = 0 := by
  have hset : {n | ∃ s : Multiset GameForm, IsFactorisation s 0 ∧ Multiset.card s = n} = {0} := by
    ext n
    constructor
    · rintro ⟨s, hs, rfl⟩
      have := (card_pos_iff_of_isFactorisation isLde_zero hs).not.mpr (by simp)
      simp only [not_lt, Nat.le_zero] at this
      exact this
    · rintro rfl
      exact ⟨0, ⟨by simp, by rw [Multiset.sum_zero]; exact fun _ _ => rfl⟩, rfl⟩
  rw [longestFactorisationLen, hset, csSup_singleton]

theorem longestFactorisationLen_isLdeAtom {a : GameForm} (ha : IsLdeAtom a) :
    longestFactorisationLen a = 1 := by
  have hfac : IsFactorisation {a} a :=
    ⟨fun b hb => by rwa [Multiset.mem_singleton.mp hb], by
      rw [Multiset.sum_singleton]; exact fun _ _ => rfl⟩
  refine le_antisymm ?_ (by simpa using card_le_longestFactorisationLen ha.1 hfac)
  obtain ⟨s, hs, hcard⟩ := exists_isFactorisation_card_longestFactorisationLen ha.1
  by_contra hlt
  push_neg at hlt
  obtain ⟨b, t, rfl⟩ : ∃ b t, s = b ::ₘ t := by
    have hs_ne : s ≠ 0 := by
      rintro rfl
      rw [Multiset.card_zero] at hcard
      omega
    obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hs_ne
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hb
    exact ⟨b, t, ht⟩
  have hb_atom : IsLdeAtom b := hs.1 b (Multiset.mem_cons_self b t)
  have ht_lde : ∀ c ∈ t, IsLde c := fun c hc => (hs.1 c (Multiset.mem_cons_of_mem hc)).1
  have ht0 : t.sum ≠ 0 := by
    have hrace := card_le_race_sum (fun c hc => hs.1 c (Multiset.mem_cons_of_mem hc))
    rw [Multiset.card_cons] at hcard
    intro hc
    rw [hc, (lde_race_zero_iff isLde_zero).mpr rfl] at hrace
    omega
  rcases ha.2.2 b t.sum hb_atom.1 (isLde_sum ht_lde)
    (hs.2.symm.trans (by rw [Multiset.sum_cons]; exact fun _ _ => rfl)) with h | h
  · exact hb_atom.2.1 h
  · exact ht0 h

theorem isLdeAtom_of_longestLen_le_one {g : GameForm} (hg : IsLde g) (hg0 : g ≠ 0)
    (hL : longestFactorisationLen g ≤ 1) : IsLdeAtom g := by
  obtain ⟨s, hs, hcard⟩ := exists_isFactorisation_card_longestFactorisationLen hg
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp (le_antisymm (by omega)
    ((card_pos_iff_of_isFactorisation hg hs).mpr hg0))
  exact (hs.1 a (Multiset.mem_singleton_self a)).of_misereEQ hg (by simpa using hs.2)

private theorem uniquelyFactorisable_of_longestLen_le_one {g : GameForm} (hg : IsLde g)
    (hL : longestFactorisationLen g ≤ 1) : UniquelyFactorisable g := by
  intro s t hs ht
  by_cases hg0 : g = 0
  · have hs0 : s = 0 := Multiset.card_eq_zero.mp (by
      have := (card_pos_iff_of_isFactorisation hg hs).not.mpr (not_not_intro hg0); omega)
    have ht0 : t = 0 := Multiset.card_eq_zero.mp (by
      have := (card_pos_iff_of_isFactorisation hg ht).not.mpr (not_not_intro hg0); omega)
    rw [hs0, ht0]
    exact Multiset.Rel.zero
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp (le_antisymm
      (le_trans (card_le_longestFactorisationLen hg hs) hL)
      ((card_pos_iff_of_isFactorisation hg hs).mpr hg0))
    obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp (le_antisymm
      (le_trans (card_le_longestFactorisationLen hg ht) hL)
      ((card_pos_iff_of_isFactorisation hg ht).mpr hg0))
    exact Multiset.Rel.cons
      ((by simpa using hs.2 : a ≡ₗ g).trans (by simpa using ht.2 : b ≡ₗ g).symm)
      Multiset.Rel.zero

/-! ## Uniqueness of factorisations -/

theorem LdeDvd.of_misereEQ {p x y : GameForm} (h : LdeDvd p x) (heq : x ≡ₗ y) : LdeDvd p y :=
  let ⟨m, hm, hx⟩ := h; ⟨m, hm, heq.symm.trans hx⟩

theorem LdeDvd.of_misereEQ_left {p q x : GameForm} (hp : IsLde p)
    (heq : p ≡ₗ q) (h : LdeDvd q x) : LdeDvd p x :=
  let ⟨m, hm, hx⟩ := h
  ⟨m, hm, hx.trans (Form.MisereQuotient.add_misereEQ_add hm.shortDeadEnding hp.shortDeadEnding
    heq.symm (fun _ _ => rfl))⟩

theorem IsLdePrime.of_misereEQ {p q : GameForm} (hp : IsLdePrime p) (hq : IsLde q)
    (heq : p ≡ₗ q) : IsLdePrime q := by
  refine ⟨hq, fun hc => hp.2.1 ((lde_misereEQ_zero_iff hp.1).mp (by rw [hc] at heq; exact heq)),
    fun h k hh hk hdvd => ?_⟩
  rcases hp.2.2 h k hh hk (LdeDvd.of_misereEQ_left hp.1 heq hdvd) with h' | h'
  · exact Or.inl (LdeDvd.of_misereEQ_left hq heq.symm h')
  · exact Or.inr (LdeDvd.of_misereEQ_left hq heq.symm h')

theorem misereEQ_of_isLdePrime_dvd_isLdeAtom {p a : GameForm} (hp : IsLdePrime p)
    (ha : IsLdeAtom a) (hdvd : LdeDvd p a) : a ≡ₗ p := by
  obtain ⟨k, hk, hak⟩ := hdvd
  rcases ha.2.2 p k hp.1 hk hak with h | h
  · exact absurd h hp.2.1
  · rw [h, add_zero] at hak
    exact hak

theorem exists_mem_of_isLdePrime_dvd_sum {p : GameForm} (hp : IsLdePrime p)
    {s : Multiset GameForm} (hs : ∀ a ∈ s, IsLde a) (hdvd : LdeDvd p s.sum) :
    ∃ a ∈ s, LdeDvd p a := by
  induction s using Multiset.induction with
  | empty =>
    exfalso
    obtain ⟨k, hk, h0⟩ := hdvd
    rw [Multiset.sum_zero] at h0
    have hz : p + k = 0 := (lde_misereEQ_zero_iff (hp.1.add hk)).mp h0.symm
    refine hp.2.1 ((lde_race_zero_iff hp.1).mp ?_)
    have := race_add hp.1 hk
    rw [hz, (lde_race_zero_iff isLde_zero).mpr rfl] at this
    omega
  | cons a t ih =>
    have ha_lde : IsLde a := hs a (Multiset.mem_cons_self a t)
    have ht_lde : ∀ b ∈ t, IsLde b := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    rw [Multiset.sum_cons] at hdvd
    rcases hp.2.2 a t.sum ha_lde (isLde_sum ht_lde) hdvd with h | h
    · exact ⟨a, Multiset.mem_cons_self a t, h⟩
    · obtain ⟨b, hb, hbd⟩ := ih ht_lde h
      exact ⟨b, Multiset.mem_cons_of_mem hb, hbd⟩

theorem misereRel_symm {s t : Multiset GameForm}
    (h : Multiset.Rel (MisereEQ Form.DeadEnding.ShortDeadEnding) s t) :
    Multiset.Rel (MisereEQ Form.DeadEnding.ShortDeadEnding) t s := by
  induction h with
  | zero => exact Multiset.Rel.zero
  | cons hab _ ih => exact Multiset.Rel.cons hab.symm ih

instance : IsTrans GameForm (MisereEQ Form.DeadEnding.ShortDeadEnding) :=
  ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩

private theorem ldeGt_add_iff {a b h : GameForm} (ha : IsLde a) (hb : IsLde b) (hh : IsLde h) :
    LdeGt (a + h) (b + h) ↔ LdeGt a b := by
  constructor
  · rintro ⟨hge, hnge⟩
    exact ⟨lde_pocancellative ha hb hh hge,
      fun hc => hnge (Form.MisereQuotient.add_misereGE_add_right hh.shortDeadEnding hc)⟩
  · rintro ⟨hge, hnge⟩
    exact ⟨Form.MisereQuotient.add_misereGE_add_right hh.shortDeadEnding hge,
      fun hc => hnge (lde_pocancellative hb ha hh hc)⟩

/--
If $G + H$ is a sum of Left dead ends, and $G' + H$ is a good option of $G + H$, then $G'$
is a good option of $G$.

This is [Davies (Lemma 7.7 on p. 35)][davies:FactorisationsLeftDead:2024].
-/
theorem isGoodOption_of_add_isGoodOption {g h gr : GameForm} (hg : IsLde g) (hh : IsLde h)
    (hgr : gr ∈ moves .right g) (hgood : IsGoodOption (gr + h) (g + h)) : IsGoodOption gr g := by
  refine ⟨hgr, ?_⟩
  rintro ⟨gr', hgr'_mem, hgt⟩
  refine hgood.2 ⟨gr' + h, ?_, ?_⟩
  · rw [moves_add]
    exact Or.inl ⟨gr', hgr'_mem, rfl⟩
  · exact (ldeGt_add_iff (hg.of_mem_rightMoves hgr) (hg.of_mem_rightMoves hgr'_mem) hh).mpr hgt

/--
If $G$ is a Left dead end, then, for every $n \in \mathbb{N}_1$, $G'$ is a good option of
$G$ if and only if $G' + (n - 1) \cdot G$ is a good option of $n \cdot G$.

This is [Davies (Lemma 7.13 on p. 38)][davies:FactorisationsLeftDead:2024].
-/
theorem isGoodOption_add_nsmul_iff {g gr : GameForm} (hg : IsLde g)
    (hgr : gr ∈ moves .right g) (n : ℕ) :
    IsGoodOption (gr + n • g) ((n + 1) • g) ↔ IsGoodOption gr g := by
  have hgr_lde : IsLde gr := hg.of_mem_rightMoves hgr
  have hn_lde : IsLde (n • g) := isLde_nsmul hg n
  constructor
  · intro hgood
    refine isGoodOption_of_add_isGoodOption hg hn_lde hgr ?_
    rwa [← succ_nsmul']
  · refine fun hgood => ⟨add_nsmul_mem_rightMoves hgr n, ?_⟩
    rintro ⟨x, hx_mem, hgt⟩
    obtain ⟨gr', hgr'_mem, rfl⟩ := exists_eq_add_nsmul_of_mem_rightMoves n hx_mem
    exact hgood.2 ⟨gr', hgr'_mem,
      (ldeGt_add_iff hgr_lde (hg.of_mem_rightMoves hgr'_mem) hn_lde).mp hgt⟩

theorem sum_misereEQ_sum_of_rel {s t : Multiset GameForm}
    (h : Multiset.Rel (MisereEQ Form.DeadEnding.ShortDeadEnding) s t) :
    (∀ a ∈ s, IsLde a) → (∀ a ∈ t, IsLde a) → s.sum ≡ₗ t.sum := by
  induction h with
  | zero =>
    intro _ _
    exact fun _ _ => rfl
  | @cons a b s' t' hab _ ih =>
    intro hs ht
    have hs'_lde : ∀ c ∈ s', IsLde c := fun c hc => hs c (Multiset.mem_cons_of_mem hc)
    have ht'_lde : ∀ c ∈ t', IsLde c := fun c hc => ht c (Multiset.mem_cons_of_mem hc)
    rw [Multiset.sum_cons, Multiset.sum_cons]
    exact Form.MisereQuotient.add_misereEQ_add (isLde_sum hs'_lde).shortDeadEnding
      (ht b (Multiset.mem_cons_self b t')).shortDeadEnding hab (ih hs'_lde ht'_lde)

/--
If $G = J + p_1 + \cdots + p_m$ with every $p_i$ prime, then every factorisation of $G$
splits as atoms matching the $p_i$ one-for-one together with a factorisation of $J$.
-/
theorem exists_split_isFactorisation_of_primes {G : GameForm} (hG : IsLde G)
    {u : Multiset GameForm} (hu : ∀ p ∈ u, IsLdePrime p)
    {s : Multiset GameForm} (hs : IsFactorisation s (G + u.sum)) :
    ∃ v w, s = v + w ∧ Multiset.Rel (MisereEQ Form.DeadEnding.ShortDeadEnding) v u ∧
      IsFactorisation w G := by
  induction u using Multiset.induction generalizing s with
  | empty =>
    refine ⟨0, s, by rw [Multiset.zero_add], Multiset.Rel.zero, hs.1, ?_⟩
    have := hs.2
    rwa [Multiset.sum_zero, add_zero] at this
  | cons p u ih =>
    have hp : IsLdePrime p := hu p (Multiset.mem_cons_self p u)
    have hu' : ∀ q ∈ u, IsLdePrime q := fun q hq => hu q (Multiset.mem_cons_of_mem hq)
    have husum_lde : IsLde u.sum := isLde_sum fun q hq => (hu' q hq).1
    have hs_lde : ∀ a ∈ s, IsLde a := fun a ha => (hs.1 a ha).1
    -- `p` divides the sum of the factorisation, hence divides one of its atoms.
    have hdvd : LdeDvd p s.sum := by
      refine ⟨G + u.sum, hG.add husum_lde, ?_⟩
      refine hs.2.trans ?_
      rw [Multiset.sum_cons, ← add_assoc, add_comm G p, add_assoc]
      exact fun _ _ => rfl
    obtain ⟨a, ha_mem, ha_dvd⟩ := exists_mem_of_isLdePrime_dvd_sum hp hs_lde hdvd
    have ha_atom : IsLdeAtom a := hs.1 a ha_mem
    have ha_p : a ≡ₗ p := misereEQ_of_isLdePrime_dvd_isLdeAtom hp ha_atom ha_dvd
    obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem ha_mem
    -- cancel `a ≡ₗ p` off both sides
    have hs'_fac : IsFactorisation s' (G + u.sum) := by
      refine ⟨fun b hb => hs.1 b (Multiset.mem_cons_of_mem hb), ?_⟩
      refine lde_cancellative (isLde_sum fun b hb => hs_lde b (Multiset.mem_cons_of_mem hb))
        (hG.add husum_lde) hp.1 ?_
      have hleft : (s'.sum + p) ≡ₗ (a ::ₘ s').sum := by
        rw [Multiset.sum_cons, add_comm a s'.sum]
        exact Form.MisereQuotient.add_misereEQ_add hp.1.shortDeadEnding
          (isLde_sum fun b hb => hs_lde b (Multiset.mem_cons_of_mem hb)).shortDeadEnding
          (fun _ _ => rfl) ha_p.symm
      refine hleft.trans (hs.2.trans ?_)
      rw [Multiset.sum_cons, ← add_assoc, add_comm G p, add_assoc, add_comm (G + u.sum) p]
      exact fun _ _ => rfl
    obtain ⟨v, w, rfl, hvu, hw⟩ := ih hu' hs'_fac
    exact ⟨a ::ₘ v, w, (Multiset.cons_add a v w).symm, Multiset.Rel.cons ha_p hvu, hw⟩

theorem UniquelyFactorisable.of_misereEQ {g h : GameForm} (hgu : UniquelyFactorisable g)
    (heq : g ≡ₗ h) : UniquelyFactorisable h :=
  fun s t hs ht => hgu s t ⟨hs.1, hs.2.trans heq.symm⟩ ⟨ht.1, ht.2.trans heq.symm⟩

theorem IsLdeAtom.uniquelyFactorisable {a : GameForm} (ha : IsLdeAtom a) :
    UniquelyFactorisable a :=
  uniquelyFactorisable_of_longestLen_le_one ha.1 (by rw [longestFactorisationLen_isLdeAtom ha])

theorem isLdePrime_of_mem_isFactorisation_of_isPrimeFactorisable {x : GameForm}
    (hpf : IsPrimeFactorisable x) {w : Multiset GameForm} (hw : IsFactorisation w x)
    {a : GameForm} (ha : a ∈ w) : IsLdePrime a := by
  obtain ⟨u, hu, husum⟩ := hpf
  have hw0 : IsFactorisation w (0 + u.sum) := by
    refine ⟨hw.1, ?_⟩
    rw [zero_add]
    exact hw.2.trans husum.symm
  obtain ⟨v, z, hsplit, hvu, hz⟩ := exists_split_isFactorisation_of_primes isLde_zero hu hw0
  have hz0 : z = 0 := Multiset.card_eq_zero.mp (by
    have := (card_pos_iff_of_isFactorisation isLde_zero hz).not.mpr (not_not_intro rfl)
    omega)
  rw [hz0, add_zero] at hsplit
  obtain ⟨p, hp_mem, hap⟩ := Multiset.exists_mem_of_rel_of_mem hvu (hsplit ▸ ha)
  exact (hu p hp_mem).of_misereEQ (hw.1 a ha).1 hap.symm

theorem isLdePrime_of_isLdeAtom_dvd {a x : GameForm} (ha : IsLdeAtom a)
    (hpf : IsPrimeFactorisable x) (hdvd : LdeDvd a x) : IsLdePrime a := by
  obtain ⟨k, hk, hxk⟩ := hdvd
  obtain ⟨w, hw⟩ := lde_atomic hk
  refine isLdePrime_of_mem_isFactorisation_of_isPrimeFactorisable hpf
    (w := a ::ₘ w) ⟨fun b hb => ?_, ?_⟩ (Multiset.mem_cons_self a w)
  · rcases Multiset.mem_cons.mp hb with rfl | hb'
    · exact ha
    · exact hw.1 b hb'
  · rw [Multiset.sum_cons]
    exact (Form.MisereQuotient.add_misereEQ_add
      (isLde_sum fun b hb => (hw.1 b hb).1).shortDeadEnding ha.1.shortDeadEnding
      (fun _ _ => rfl) hw.2).trans hxk.symm

theorem isPrimeFactorisable_of_dvd {x y : GameForm} (hx : IsLde x)
    (hpf : IsPrimeFactorisable y) (hdvd : LdeDvd x y) : IsPrimeFactorisable x := by
  obtain ⟨k, hk, hyk⟩ := hdvd
  obtain ⟨w, hw⟩ := lde_atomic hx
  obtain ⟨w', hw'⟩ := lde_atomic hk
  have hfac : IsFactorisation (w + w') y := by
    refine ⟨fun b hb => ?_, ?_⟩
    · rcases Multiset.mem_add.mp hb with hb' | hb'
      · exact hw.1 b hb'
      · exact hw'.1 b hb'
    · rw [Multiset.sum_add]
      exact (Form.MisereQuotient.add_misereEQ_add
        (isLde_sum fun b hb => (hw'.1 b hb).1).shortDeadEnding hx.shortDeadEnding
        hw.2 hw'.2).trans hyk.symm
  exact ⟨w, fun p hp => isLdePrime_of_mem_isFactorisation_of_isPrimeFactorisable hpf hfac
    (Multiset.mem_add.mpr (Or.inl hp)), hw.2⟩

theorem IsPrimeFactorisable.add {x y : GameForm} (hx : IsLde x)
    (hxp : IsPrimeFactorisable x) (hyp : IsPrimeFactorisable y) :
    IsPrimeFactorisable (x + y) := by
  obtain ⟨u, hu, husum⟩ := hxp
  obtain ⟨v, hv, hvsum⟩ := hyp
  refine ⟨u + v, fun p hp => ?_, ?_⟩
  · rcases Multiset.mem_add.mp hp with hp' | hp'
    · exact hu p hp'
    · exact hv p hp'
  · rw [Multiset.sum_add]
    exact Form.MisereQuotient.add_misereEQ_add
      (isLde_sum fun p hp => (hv p hp).1).shortDeadEnding hx.shortDeadEnding husum hvsum

theorem IsPrimeFactorisable.nsmul {x : GameForm} (hx : IsLde x) (hxp : IsPrimeFactorisable x) :
    ∀ n : ℕ, IsPrimeFactorisable (n • x)
  | 0 => ⟨0, by simp, by rw [zero_nsmul, Multiset.sum_zero]; exact fun _ _ => rfl⟩
  | n + 1 => by
    rw [succ_nsmul]
    exact IsPrimeFactorisable.add (isLde_nsmul hx n)
      (IsPrimeFactorisable.nsmul hx hxp n) hxp

/--
Every longest factorisation of $G$ is of the form $H_1 + \cdots + H_k + K$, where
$H_1 + \cdots + H_k$ is a longest factorisation of $H$.

This is [Davies (Proposition 7.1(3) on p. 32)][davies:FactorisationsLeftDead:2024].
-/
theorem isFactorisation_erase_of_longestLen_eq {g h : GameForm} (hg : IsLde g) (hh : IsLde h)
    (hgood : IsGoodOption h g)
    (hlen : longestFactorisationLen g = longestFactorisationLen h + 1)
    {s : Multiset GameForm} (hs : IsFactorisation s g)
    (hcard : Multiset.card s = longestFactorisationLen g) :
    ∃ a t, s = a ::ₘ t ∧ IsLdeAtom a ∧ race a = 1 ∧ IsFactorisation t h ∧
      Multiset.card t = longestFactorisationLen h := by
  have hs_lde : ∀ a ∈ s, IsLde a := fun a ha => (hs.1 a ha).1
  have hsum_lde : IsLde s.sum := isLde_sum hs_lde
  obtain ⟨y, hy_good, hy_eq⟩ := lde_good_option_misereEQ hg hsum_lde hs.2.symm hgood
  obtain ⟨a, t, rfl, ar, har, rfl⟩ := exists_eq_add_sum_of_mem_rightMoves_sum hy_good.1
  have ha_atom : IsLdeAtom a := hs.1 a (Multiset.mem_cons_self a t)
  have ha_lde : IsLde a := ha_atom.1
  have ht_lde : ∀ b ∈ t, IsLde b := fun b hb => hs_lde b (Multiset.mem_cons_of_mem hb)
  have htsum_lde : IsLde t.sum := isLde_sum ht_lde
  have har_lde : IsLde ar := ha_lde.of_mem_rightMoves har
  rw [Multiset.card_cons] at hcard
  -- `ar = 0`, else `h` would have too long a factorisation.
  have har0 : ar = 0 := by
    by_contra hne
    obtain ⟨u, hu⟩ := lde_atomic har_lde
    have hu_ne : u ≠ 0 := by
      rintro rfl
      exact hne ((lde_misereEQ_zero_iff har_lde).mp (by simpa using hu.2.symm))
    have hut : IsFactorisation (u + t) h := by
      refine ⟨fun b hb => ?_, ?_⟩
      · rcases Multiset.mem_add.mp hb with hb' | hb'
        · exact hu.1 b hb'
        · exact hs.1 b (Multiset.mem_cons_of_mem hb')
      · rw [Multiset.sum_add]
        exact (Form.MisereQuotient.add_misereEQ_add htsum_lde.shortDeadEnding
          har_lde.shortDeadEnding hu.2 (fun _ _ => rfl)).trans hy_eq.symm
    have hle := card_le_longestFactorisationLen hh hut
    have hu_pos : 0 < Multiset.card u := Multiset.card_pos.mpr hu_ne
    rw [Multiset.card_add] at hle
    omega
  subst har0
  have ht_h : t.sum ≡ₗ h := (by simpa using (hy_eq.symm : (0 + t.sum) ≡ₗ h))
  refine ⟨a, t, rfl, ha_atom, ?_, ⟨fun b hb => hs.1 b (Multiset.mem_cons_of_mem hb), ht_h⟩,
    by omega⟩
  -- `a` moves to `0`, so it is terminable.
  have hle := race_le_succ_race_of_mem_rightMoves ha_lde har
  rw [(lde_race_zero_iff isLde_zero).mpr rfl] at hle
  have := (lde_race_zero_iff ha_lde).not.mpr ha_atom.2.1
  omega

/--
There exists an atom $K$ such that $G = H + K$, and $K$ is terminable.

This is the existence half of
[Davies (Proposition 7.1(2) on p. 32)][davies:FactorisationsLeftDead:2024].
-/
theorem exists_isLdeAtom_add_of_longestLen_eq {g h : GameForm} (hg : IsLde g) (hh : IsLde h)
    (hgood : IsGoodOption h g)
    (hlen : longestFactorisationLen g = longestFactorisationLen h + 1) :
    ∃ k, IsLdeAtom k ∧ race k = 1 ∧ (g ≡ₗ (h + k)) := by
  obtain ⟨s, hs, hcard⟩ := exists_isFactorisation_card_longestFactorisationLen hg
  obtain ⟨a, t, rfl, ha_atom, hrace, ht, -⟩ :=
    isFactorisation_erase_of_longestLen_eq hg hh hgood hlen hs hcard
  refine ⟨a, ha_atom, hrace, hs.2.symm.trans ?_⟩
  rw [Multiset.sum_cons, add_comm]
  exact Form.MisereQuotient.add_misereEQ_add ha_atom.1.shortDeadEnding hh.shortDeadEnding
    ht.2 (fun _ _ => rfl)

/--
If $G$ is a Left dead end with a good option $H$ such that
$\overline{\mathsf{L}(G)} = \overline{\mathsf{L}(H)} + 1$, then

1. $H$ is a racing option of $G$; and

2. there exists a unique atom $K$ such that $G = H + K$, and $K$ is terminable.

This is [Davies (Proposition 7.1 on p. 32)][davies:FactorisationsLeftDead:2024].
-/
theorem isRacingOption_and_exists_unique_isLdeAtom_add {g h : GameForm} (hg : IsLde g)
    (hh : IsLde h) (hgood : IsGoodOption h g)
    (hlen : longestFactorisationLen g = longestFactorisationLen h + 1) :
    IsRacingOption h g ∧ ∃ k, IsLdeAtom k ∧ race k = 1 ∧ (g ≡ₗ (h + k)) ∧
      ∀ k', IsLdeAtom k' → (g ≡ₗ (h + k')) → k' ≡ₗ k := by
  obtain ⟨k, hk_atom, hk_race, hk_eq⟩ :=
    exists_isLdeAtom_add_of_longestLen_eq hg hh hgood hlen
  have hracing : IsRacingOption h g := by
    refine ⟨hgood.1, ?_⟩
    rw [race_eq_of_misereEQ hg (hh.add hk_atom.1) hk_eq, race_add hh hk_atom.1, hk_race]
  refine ⟨hracing, k, hk_atom, hk_race, hk_eq, fun k' hk' heq' => ?_⟩
  refine lde_cancellative hk'.1 hk_atom.1 hh ?_
  rw [add_comm k' h, add_comm k h]
  exact heq'.symm.trans hk_eq

/--
If $G$ is a Left dead end with a good option to an atom $H$, then either $G$ is an atom,
or $H$ is a racing option of $G$ and there exists a unique (terminable) atom $K$ such that
$G = H + K$; in particular, $G$ is uniquely factorisable.

This is the "in particular" of
[Davies (Corollary 7.2 on p. 33)][davies:FactorisationsLeftDead:2024].
-/
theorem uniquelyFactorisable_of_good_atom {g h : GameForm} (hg : IsLde g)
    (hh : IsLdeAtom h) (hgo : IsGoodOption h g) : UniquelyFactorisable g := by
  -- Lemma 6.1 with `L(h) = 1` caps `L(g)` at `2`.
  have hL2 : longestFactorisationLen g ≤ 2 := by
    have := longestLen_le_good_option hg hgo
    rwa [longestFactorisationLen_isLdeAtom hh] at this
  rcases Nat.lt_or_ge (longestFactorisationLen g) 2 with hlt | hge
  · exact uniquelyFactorisable_of_longestLen_le_one hg (by omega)
  have hLg : longestFactorisationLen g = 2 := by omega
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [longestFactorisationLen_zero] at hLg
    exact absurd hLg (by decide)
  have hlen : longestFactorisationLen g = longestFactorisationLen h + 1 := by
    rw [hLg, longestFactorisationLen_isLdeAtom hh]
  -- Every factorisation of `g` is longest, hence of the shape `{a, b}` with `b ≡ₗ h`.
  have key : ∀ s, IsFactorisation s g → ∃ a b, s = {a, b} ∧ (b ≡ₗ h) ∧ (g ≡ₗ (a + h)) := by
    intro s hs
    have hcard : Multiset.card s = longestFactorisationLen g := by
      refine le_antisymm (card_le_longestFactorisationLen hg hs) ?_
      -- a factorisation of length 1 would make `g` an atom, forcing `L(g) = 1`
      rcases Nat.lt_or_ge (Multiset.card s) 2 with h1 | h1
      · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp (le_antisymm (by omega)
          ((card_pos_iff_of_isFactorisation hg hs).mpr hg0))
        rw [← longestFactorisationLen_eq_of_misereEQ (show a ≡ₗ g by simpa using hs.2),
          longestFactorisationLen_isLdeAtom (hs.1 a (Multiset.mem_singleton_self a))] at hLg
        exact absurd hLg (by decide)
      · omega
    obtain ⟨a, t, rfl, ha_atom, -, ht, htcard⟩ :=
      isFactorisation_erase_of_longestLen_eq hg hh.1 hgo hlen hs hcard
    rw [longestFactorisationLen_isLdeAtom hh] at htcard
    obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp htcard
    have hb_eq : b ≡ₗ h := by simpa using ht.2
    have hb_lde : IsLde b := (ht.1 b (Multiset.mem_singleton_self b)).1
    refine ⟨a, b, rfl, hb_eq, hs.2.symm.trans ?_⟩
    rw [Multiset.sum_cons, Multiset.sum_singleton]
    exact Form.MisereQuotient.add_misereEQ_add hb_lde.shortDeadEnding ha_atom.1.shortDeadEnding
      (fun _ _ => rfl) hb_eq
  intro s t hs ht
  obtain ⟨a, b, rfl, hb, hga⟩ := key s hs
  obtain ⟨a', b', rfl, hb', hga'⟩ := key t ht
  have haa' : a ≡ₗ a' :=
    lde_cancellative (hs.1 a (by simp)).1 (ht.1 a' (by simp)).1 hh.1 (hga.symm.trans hga')
  exact Multiset.Rel.cons haa' (Multiset.Rel.cons (hb.trans hb'.symm) Multiset.Rel.zero)

/--
If $G$ is a Left dead end with good options to distinct atoms $H$ and $K$, then either $G$
is an atom, or $H + K$ is the unique factorisation of $G$.

This is [Davies (Corollary 7.3 on p. 33)][davies:FactorisationsLeftDead:2024].
-/
theorem isLdeAtom_or_isFactorisation_of_good_atoms {g h k : GameForm} (hg : IsLde g)
    (hh : IsLdeAtom h) (hk : IsLdeAtom k) (hgh : IsGoodOption h g) (hgk : IsGoodOption k g)
    (hne : ¬ (h ≡ₗ k)) : IsLdeAtom g ∨ IsFactorisation {h, k} g := by
  by_cases hatom : IsLdeAtom g
  · exact Or.inl hatom
  refine Or.inr ?_
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact absurd hgh.1 (by simp)
  -- `g` is not an atom, so `L(g) = 2` by Lemma 6.1 applied to the good option `h`.
  have hL2 : longestFactorisationLen g ≤ 2 := by
    have := longestLen_le_good_option hg hgh
    rwa [longestFactorisationLen_isLdeAtom hh] at this
  have hLg : longestFactorisationLen g = 2 := by
    rcases Nat.lt_or_ge (longestFactorisationLen g) 2 with hlt | hge
    · exact absurd (isLdeAtom_of_longestLen_le_one hg hg0 (by omega)) hatom
    · omega
  -- Proposition 7.1 with the good option `h` splits off an atom `j`.
  obtain ⟨j, hj_atom, -, hj_eq⟩ := exists_isLdeAtom_add_of_longestLen_eq hg hh.1 hgh
    (by rw [hLg, longestFactorisationLen_isLdeAtom hh])
  have hfac : IsFactorisation {h, j} g := by
    refine ⟨fun b hb => ?_, ?_⟩
    · rcases Multiset.mem_cons.mp hb with rfl | hb'
      · exact hh
      · rwa [Multiset.mem_singleton.mp hb']
    · simpa using hj_eq.symm
  -- Feed that longest factorisation back through Proposition 7.1(3), now with `k`.
  obtain ⟨a, t, heqs, -, -, ht, htcard⟩ := isFactorisation_erase_of_longestLen_eq hg hk.1 hgk
    (by rw [hLg, longestFactorisationLen_isLdeAtom hk]) hfac (by simp [hLg])
  rw [longestFactorisationLen_isLdeAtom hk] at htcard
  obtain ⟨c, rfl⟩ := Multiset.card_eq_one.mp htcard
  have hc_k : c ≡ₗ k := by simpa using ht.2
  have hc_mem : c ∈ ({h, j} : Multiset GameForm) := by
    rw [heqs]
    exact Multiset.mem_cons_of_mem (Multiset.mem_singleton_self c)
  -- `c ≡ₗ k` rules out `c = h`, so `c = j` and hence `j ≡ₗ k`.
  have hjk : j ≡ₗ k := by
    rcases Multiset.mem_cons.mp hc_mem with rfl | hc'
    · exact absurd hc_k hne
    · rwa [Multiset.mem_singleton.mp hc'] at hc_k
  refine ⟨fun b hb => ?_, ?_⟩
  · rcases Multiset.mem_cons.mp hb with rfl | hb'
    · exact hh
    · rwa [Multiset.mem_singleton.mp hb']
  · have hsum : (h + k) ≡ₗ g :=
      (Form.MisereQuotient.add_misereEQ_add hk.1.shortDeadEnding hh.1.shortDeadEnding
        (fun _ _ => rfl) hjk.symm).trans hj_eq.symm
    simpa using hsum

/--
If either of $H$ or $K$ is not terminable (i.e. if $r(G) \ne 2$), then $G$ is an atom.

This is the "in particular" of
[Davies (Corollary 7.3 on p. 33)][davies:FactorisationsLeftDead:2024].
-/
theorem isLdeAtom_of_good_atoms_of_race_ne_two {g h k : GameForm} (hg : IsLde g)
    (hh : IsLdeAtom h) (hk : IsLdeAtom k) (hgh : IsGoodOption h g) (hgk : IsGoodOption k g)
    (hne : ¬ (h ≡ₗ k)) (hrace : race g ≠ 2) : IsLdeAtom g := by
  rcases isLdeAtom_or_isFactorisation_of_good_atoms hg hh hk hgh hgk hne with hatom | hfac
  · exact hatom
  exfalso
  -- Proposition 7.1 makes each of `h`, `k` terminable, so `r(g) = 1 + 1`.
  have hLg : longestFactorisationLen g = 2 := by
    refine le_antisymm ?_ (by simpa using card_le_longestFactorisationLen hg hfac)
    have := longestLen_le_good_option hg hgh
    rwa [longestFactorisationLen_isLdeAtom hh] at this
  have hsum : (h + k) ≡ₗ g := by simpa using hfac.2
  -- Proposition 7.1 on the good option `h` splits off a terminable atom `j` with
  -- `g ≡ₗ h + j`; cancelling `h` against `g ≡ₗ h + k` identifies `j ≡ₗ k`, so `r(k) = 1`.
  obtain ⟨j, hj_atom, hj_race, hj_eq⟩ := exists_isLdeAtom_add_of_longestLen_eq hg hh.1 hgh
    (by rw [hLg, longestFactorisationLen_isLdeAtom hh])
  obtain ⟨j', hj'_atom, hj'_race, hj'_eq⟩ := exists_isLdeAtom_add_of_longestLen_eq hg hk.1 hgk
    (by rw [hLg, longestFactorisationLen_isLdeAtom hk])
  have hkj : k ≡ₗ j := by
    refine lde_cancellative hk.1 hj_atom.1 hh.1 ?_
    rw [add_comm k h, add_comm j h]
    exact hsum.trans hj_eq
  have hhj' : h ≡ₗ j' := by
    refine lde_cancellative hh.1 hj'_atom.1 hk.1 ?_
    rw [add_comm j' k]
    exact hsum.trans hj'_eq
  refine hrace ?_
  rw [← race_eq_of_misereEQ (hh.1.add hk.1) hg hsum, race_add hh.1 hk.1,
    race_eq_of_misereEQ hh.1 hj'_atom.1 hhj', race_eq_of_misereEQ hk.1 hj_atom.1 hkj,
    hj'_race, hj_race]

/--
If $G$ is a Left dead end with at least three good options to pairwise distinct atoms,
then $G$ is an atom.

This is [Davies (Corollary 7.4 on p. 33)][davies:FactorisationsLeftDead:2024].
-/
theorem isLdeAtom_of_three_good_atoms {g a b c : GameForm} (hg : IsLde g)
    (ha : IsLdeAtom a) (hb : IsLdeAtom b) (hc : IsLdeAtom c)
    (hga : IsGoodOption a g) (hgb : IsGoodOption b g) (hgc : IsGoodOption c g)
    (hab : ¬ (a ≡ₗ b)) (hbc : ¬ (b ≡ₗ c)) (hac : ¬ (a ≡ₗ c)) : IsLdeAtom g := by
  by_cases hatom : IsLdeAtom g
  · exact hatom
  exfalso
  have hsum : ∀ {x y : GameForm}, IsLdeAtom x → IsLdeAtom y → IsGoodOption x g →
      IsGoodOption y g → ¬ (x ≡ₗ y) → (x + y) ≡ₗ g := by
    intro x y hx hy hgx hgy hxy
    rcases isLdeAtom_or_isFactorisation_of_good_atoms hg hx hy hgx hgy hxy with h | hfac
    · exact absurd h hatom
    · simpa using hfac.2
  refine hac (lde_cancellative ha.1 hc.1 hb.1 ?_)
  rw [add_comm c b]
  exact (hsum ha hb hga hgb hab).trans (hsum hb hc hgb hgc hbc).symm

private theorem factor_eq_of_good_pf_aux (n : ℕ) :
    ∀ (a : GameForm) (s' t : Multiset GameForm), IsFactorisation (a ::ₘ s') (a + s'.sum) →
      IsFactorisation t (a + s'.sum) → Multiset.card t ≤ n →
      ∀ ar ∈ moves .right a, IsGoodOption (ar + s'.sum) (a + s'.sum) →
        IsPrimeFactorisable ar → ∃ b ∈ t, a ≡ₗ b := by
  induction n with
  | zero =>
    -- vacuous: `a` is a non-zero atom, so `a + s'.sum ≠ 0` has a non-empty factorisation
    intro a s' t hs ht hcard _ _ _ _
    exfalso
    have ha_atom : IsLdeAtom a := hs.1 a (Multiset.mem_cons_self a s')
    have hs'_lde : ∀ c ∈ s', IsLde c := fun c hc => (hs.1 c (Multiset.mem_cons_of_mem hc)).1
    obtain rfl : t = 0 := Multiset.card_eq_zero.mp (by omega)
    have hz : a + s'.sum = 0 := (lde_misereEQ_zero_iff (ha_atom.1.add (isLde_sum hs'_lde))).mp
      (by simpa using ht.2.symm)
    refine ha_atom.2.1 ((lde_race_zero_iff ha_atom.1).mp ?_)
    have hr := race_add ha_atom.1 (isLde_sum hs'_lde)
    rw [hz, (lde_race_zero_iff isLde_zero).mpr rfl] at hr
    omega
  | succ n ih =>
    intro a s' t hs ht hcard ar har hgood hpf
    classical
    have ha_atom : IsLdeAtom a := hs.1 a (Multiset.mem_cons_self a s')
    have hs'_atoms : ∀ c ∈ s', IsLdeAtom c := fun c hc => hs.1 c (Multiset.mem_cons_of_mem hc)
    have hs'_lde : ∀ c ∈ s', IsLde c := fun c hc => (hs'_atoms c hc).1
    have hs'sum_lde : IsLde s'.sum := isLde_sum hs'_lde
    have ht_lde : ∀ c ∈ t, IsLde c := fun c hc => (ht.1 c hc).1
    have htsum_eq : t.sum ≡ₗ (a + s'.sum) := ht.2
    -- Case A: `a` itself is prime — then it divides `t.sum` and *is* one of its atoms.
    by_cases ha_prime : IsLdePrime a
    · obtain ⟨b, hb_mem, hb_dvd⟩ := exists_mem_of_isLdePrime_dvd_sum ha_prime ht_lde
        ⟨s'.sum, hs'sum_lde, htsum_eq⟩
      exact ⟨b, hb_mem, (misereEQ_of_isLdePrime_dvd_isLdeAtom ha_prime (ht.1 b hb_mem)
        hb_dvd).symm⟩
    -- Case B: some factor of `t` is prime — cancel it against its twin in `a ::ₘ s'`.
    by_cases hpt : ∃ c ∈ t, IsLdePrime c
    · obtain ⟨c, hc_mem, hc_prime⟩ := hpt
      obtain ⟨t'', rfl⟩ := Multiset.exists_cons_of_mem hc_mem
      have ht''_lde : ∀ x ∈ t'', IsLde x := fun x hx => ht_lde x (Multiset.mem_cons_of_mem hx)
      obtain ⟨d, hd_mem, hd_dvd⟩ := exists_mem_of_isLdePrime_dvd_sum hc_prime
        (fun x hx => (hs.1 x hx).1) ⟨t''.sum, isLde_sum ht''_lde, by
          refine hs.2.trans (htsum_eq.symm.trans ?_)
          rw [Multiset.sum_cons]
          exact fun _ _ => rfl⟩
      have hdc : d ≡ₗ c := misereEQ_of_isLdePrime_dvd_isLdeAtom hc_prime (hs.1 d hd_mem) hd_dvd
      rcases Multiset.mem_cons.mp hd_mem with rfl | hd_s'
      · exact ⟨c, Multiset.mem_cons_self c t'', hdc⟩
      obtain ⟨s'', rfl⟩ := Multiset.exists_cons_of_mem hd_s'
      have hd_lde : IsLde d := hs'_lde d (Multiset.mem_cons_self d s'')
      have hs''_lde : ∀ x ∈ s'', IsLde x := fun x hx => hs'_lde x (Multiset.mem_cons_of_mem hx)
      have hs''sum_lde : IsLde s''.sum := isLde_sum hs''_lde
      -- the smaller pair of factorisations, of `a + s''.sum`
      have hs2 : IsFactorisation (a ::ₘ s'') (a + s''.sum) := by
        refine ⟨fun x hx => ?_, by rw [Multiset.sum_cons]; exact fun _ _ => rfl⟩
        rcases Multiset.mem_cons.mp hx with rfl | hx'
        · exact ha_atom
        · exact hs'_atoms x (Multiset.mem_cons_of_mem hx')
      have ht2 : IsFactorisation t'' (a + s''.sum) := by
        refine ⟨fun x hx => ht.1 x (Multiset.mem_cons_of_mem hx), ?_⟩
        refine lde_cancellative (isLde_sum ht''_lde) (ha_atom.1.add hs''sum_lde) hd_lde ?_
        have hleft : (t''.sum + d) ≡ₗ (c + t''.sum) := by
          rw [add_comm c t''.sum]
          exact Form.MisereQuotient.add_misereEQ_add hd_lde.shortDeadEnding
            (isLde_sum ht''_lde).shortDeadEnding (fun _ _ => rfl) hdc
        refine hleft.trans ?_
        rw [← Multiset.sum_cons]
        refine htsum_eq.trans ?_
        have e : a + (d ::ₘ s'').sum = a + s''.sum + d := by
          rw [Multiset.sum_cons]; ac_rfl
        rw [e]
        exact fun _ _ => rfl
      -- Lemma 7.7 strips the common summand `d` off the good option
      have hgood2 : IsGoodOption (ar + s''.sum) (a + s''.sum) := by
        refine isGoodOption_of_add_isGoodOption (ha_atom.1.add hs''sum_lde) hd_lde ?_ ?_
        · rw [moves_add]
          exact Or.inl ⟨ar, har, rfl⟩
        · have e1 : ar + s''.sum + d = ar + (d ::ₘ s'').sum := by
            rw [Multiset.sum_cons]; ac_rfl
          have e2 : a + s''.sum + d = a + (d ::ₘ s'').sum := by
            rw [Multiset.sum_cons]; ac_rfl
          rw [e1, e2]
          exact hgood
      obtain ⟨b, hb_mem, hb⟩ := ih a s'' t'' hs2 ht2
        (by rw [Multiset.card_cons] at hcard; omega) ar har hgood2 hpf
      exact ⟨b, Multiset.mem_cons_of_mem hb_mem, hb⟩
    -- Case C: no factor of `t` is prime. This is the paper's main argument.
    push_neg at hpt
    obtain ⟨u, hu, husum⟩ := hpf
    have hu_lde : ∀ p ∈ u, IsLde p := fun p hp => (hu p hp).1
    have har_lde : IsLde ar := ha_atom.1.of_mem_rightMoves har
    -- Corollary 3.4: match the good option against a good option of `t`
    obtain ⟨y, hy_good, hy_eq⟩ := lde_good_option_misereEQ (ha_atom.1.add hs'sum_lde)
      (isLde_sum ht_lde) htsum_eq.symm hgood
    obtain ⟨b, t', rfl, br, hbr, rfl⟩ := exists_eq_add_sum_of_mem_rightMoves_sum hy_good.1
    have hb_atom : IsLdeAtom b := ht.1 b (Multiset.mem_cons_self b t')
    have ht'_lde : ∀ x ∈ t', IsLde x := fun x hx => ht_lde x (Multiset.mem_cons_of_mem hx)
    have ht'sum_lde : IsLde t'.sum := isLde_sum ht'_lde
    have hbr_lde : IsLde br := hb_atom.1.of_mem_rightMoves hbr
    -- factorise `br` and split off the primes of `ar`
    obtain ⟨w, hw⟩ := lde_atomic hbr_lde
    have hw_lde : ∀ x ∈ w, IsLde x := fun x hx => (hw.1 x hx).1
    have hfac : IsFactorisation (w + t') (s'.sum + u.sum) := by
      refine ⟨fun x hx => ?_, ?_⟩
      · rcases Multiset.mem_add.mp hx with hx' | hx'
        · exact hw.1 x hx'
        · exact ht.1 x (Multiset.mem_cons_of_mem hx')
      · rw [Multiset.sum_add]
        refine (Form.MisereQuotient.add_misereEQ_add ht'sum_lde.shortDeadEnding
          hbr_lde.shortDeadEnding hw.2 (fun _ _ => rfl)).trans ?_
        refine hy_eq.symm.trans ?_
        rw [add_comm s'.sum u.sum]
        exact Form.MisereQuotient.add_misereEQ_add hs'sum_lde.shortDeadEnding
          (isLde_sum hu_lde).shortDeadEnding husum.symm (fun _ _ => rfl)
    obtain ⟨v, z, hsplit, hvu, hz⟩ := exists_split_isFactorisation_of_primes hs'sum_lde hu hfac
    -- every element of `v` is prime, no element of `t'` is; hence `v ≤ w`
    have hv_prime : ∀ x ∈ v, IsLdePrime x := by
      intro x hx
      obtain ⟨p, hp_mem, hxp⟩ := Multiset.exists_mem_of_rel_of_mem hvu hx
      refine (hu p hp_mem).of_misereEQ ?_ hxp.symm
      exact (hfac.1 x (by rw [hsplit]; exact Multiset.mem_add.mpr (Or.inl hx))).1
    have hv_le_w : v ≤ w := by
      refine Multiset.le_iff_count.mpr fun x => ?_
      rcases Nat.eq_zero_or_pos (Multiset.count x v) with hx | hx
      · omega
      have hx_nt' : x ∉ t' := fun hc =>
        hpt x (Multiset.mem_cons_of_mem hc) (hv_prime x (Multiset.count_pos.mp hx))
      have hcount : Multiset.count x w + Multiset.count x t'
          = Multiset.count x v + Multiset.count x z := by
        rw [← Multiset.count_add, ← Multiset.count_add, hsplit]
      rw [Multiset.count_eq_zero.mpr hx_nt'] at hcount
      omega
    obtain ⟨w'', rfl⟩ := Multiset.le_iff_exists_add.mp hv_le_w
    have hz_eq : z = w'' + t' := by
      have : v + (w'' + t') = v + z := by rw [← hsplit]; ac_rfl
      exact (add_left_cancel this).symm
    subst hz_eq
    have hw''_lde : ∀ x ∈ w'', IsLde x := fun x hx =>
      hw_lde x (Multiset.mem_add.mpr (Or.inr hx))
    have hw''sum_lde : IsLde w''.sum := isLde_sum hw''_lde
    -- `s'.sum ≡ₗ R + t'.sum` where `R = w''.sum`
    have hs'_split : s'.sum ≡ₗ (w''.sum + t'.sum) := by
      refine hz.2.symm.trans ?_
      rw [Multiset.sum_add]
      exact fun _ _ => rfl
    -- cancel `t'.sum`: `b ≡ₗ a + R`
    have hb_eq : b ≡ₗ (a + w''.sum) := by
      refine lde_cancellative hb_atom.1 (ha_atom.1.add hw''sum_lde) ht'sum_lde ?_
      refine (show (b + t'.sum) ≡ₗ (b ::ₘ t').sum by rw [Multiset.sum_cons]; exact fun _ _ => rfl)
        |>.trans (htsum_eq.trans ?_)
      rw [add_assoc]
      exact Form.MisereQuotient.add_misereEQ_add hs'sum_lde.shortDeadEnding
        ha_atom.1.shortDeadEnding (fun _ _ => rfl) hs'_split
    -- `b` is an atom and `a ≠ 0`, so the cofactor `R` vanishes
    rcases hb_atom.2.2 a w''.sum ha_atom.1 hw''sum_lde hb_eq with h0 | h0
    · exact absurd h0 ha_atom.2.1
    refine ⟨b, Multiset.mem_cons_self b t', ?_⟩
    rw [h0, add_zero] at hb_eq
    exact hb_eq.symm

/--
If $G := G_1 + \cdots + G_n = H_1 + \cdots + H_m =: H$ are factorisations of a Left dead
end $G$, and there is a good option of $G$ playing on the component $G_1$ to some
prime-factorisable $G'_1$, then there exists an index $j$ such that $G_1 = H_j$.

This is [Davies (Lemma 7.5 on p. 34)][davies:FactorisationsLeftDead:2024].
-/
theorem factor_eq_of_good_pf {a : GameForm} {s' t : Multiset GameForm}
    (hs : IsFactorisation (a ::ₘ s') (a + s'.sum)) (ht : IsFactorisation t (a + s'.sum))
    {ar : GameForm} (har : ar ∈ moves .right a)
    (hgood : IsGoodOption (ar + s'.sum) (a + s'.sum)) (hpf : IsPrimeFactorisable ar) :
    ∃ b ∈ t, a ≡ₗ b :=
  factor_eq_of_good_pf_aux (Multiset.card t) a s' t hs ht le_rfl ar har hgood hpf

/--
Reading a factorisation as $G_1 + \cdots + G_k$: for every $1 \le i \le k$, there exists a
good option of $G_i + \cdots + G_k$ on the component $G_i$ to some prime-factorisable
$G'_i$.

This is the hypothesis of
[Davies (Theorem 7.6 on p. 35)][davies:FactorisationsLeftDead:2024].
-/
inductive IsGoodPfChain : Multiset GameForm → Prop
  | nil : IsGoodPfChain 0
  | cons {a : GameForm} {s : Multiset GameForm} {ar : GameForm} (har : ar ∈ moves .right a)
      (hgood : IsGoodOption (ar + s.sum) (a + s.sum)) (hpf : IsPrimeFactorisable ar)
      (hrest : IsGoodPfChain s) : IsGoodPfChain (a ::ₘ s)

theorem rel_of_isGoodPfChain {s : Multiset GameForm} (hchain : IsGoodPfChain s) :
    (∀ a ∈ s, IsLdeAtom a) → ∀ t : Multiset GameForm, IsFactorisation t s.sum →
      Multiset.Rel (MisereEQ Form.DeadEnding.ShortDeadEnding) s t := by
  induction hchain with
  | nil =>
    intro _ t ht
    obtain rfl : t = 0 := Multiset.card_eq_zero.mp (by
      have := (card_pos_iff_of_isFactorisation isLde_zero (by simpa using ht)).not.mpr
        (not_not_intro rfl)
      omega)
    exact Multiset.Rel.zero
  | @cons a s ar har hgood hpf hrest ih =>
    intro hatoms t ht
    have ha_atom : IsLdeAtom a := hatoms a (Multiset.mem_cons_self a s)
    have hs_atoms : ∀ x ∈ s, IsLdeAtom x := fun x hx => hatoms x (Multiset.mem_cons_of_mem hx)
    have hssum_lde : IsLde s.sum := isLde_sum fun x hx => (hs_atoms x hx).1
    have hfacs : IsFactorisation (a ::ₘ s) (a + s.sum) :=
      ⟨hatoms, by rw [Multiset.sum_cons]; exact fun _ _ => rfl⟩
    have ht2 : IsFactorisation t (a + s.sum) := by
      refine ⟨ht.1, ht.2.trans ?_⟩
      rw [Multiset.sum_cons]
      exact fun _ _ => rfl
    obtain ⟨b, hb_mem, hab⟩ := factor_eq_of_good_pf hfacs ht2 har hgood hpf
    obtain ⟨t'', rfl⟩ := Multiset.exists_cons_of_mem hb_mem
    have ht''_lde : ∀ x ∈ t'', IsLde x := fun x hx => (ht.1 x (Multiset.mem_cons_of_mem hx)).1
    refine Multiset.Rel.cons hab (ih hs_atoms t'' ⟨fun x hx => ht.1 x (Multiset.mem_cons_of_mem hx),
      ?_⟩)
    refine lde_cancellative (isLde_sum ht''_lde) hssum_lde ha_atom.1 ?_
    have e1 : (t''.sum + a) ≡ₗ (b + t''.sum) := by
      rw [add_comm b t''.sum]
      exact Form.MisereQuotient.add_misereEQ_add ha_atom.1.shortDeadEnding
        (isLde_sum ht''_lde).shortDeadEnding (fun _ _ => rfl) hab
    refine e1.trans ?_
    rw [← Multiset.sum_cons]
    refine ht.2.trans ?_
    rw [Multiset.sum_cons, add_comm a s.sum]
    exact fun _ _ => rfl

/--
If $G := G_1 + \cdots + G_k$ is a factorisation of a Left dead end such that, for every
$1 \le i \le k$, there exists a good option of $G_i + \cdots + G_k$ on the component $G_i$
to some prime-factorisable $G'_i$, then $G$ is uniquely factorisable.

This is [Davies (Theorem 7.6 on p. 35)][davies:FactorisationsLeftDead:2024].
-/
theorem uniquelyFactorisable_of_chain {g : GameForm}
    {s : Multiset GameForm} (hs : IsFactorisation s g) (hchain : IsGoodPfChain s) :
    UniquelyFactorisable g := by
  intro t t' ht ht'
  exact Multiset.Rel.trans _
    (misereRel_symm (rel_of_isGoodPfChain hchain hs.1 t ⟨ht.1, ht.2.trans hs.2.symm⟩))
    (rel_of_isGoodPfChain hchain hs.1 t' ⟨ht'.1, ht'.2.trans hs.2.symm⟩)

theorem exists_isGoodOption_isRacingOption {g : GameForm} (hg : IsLde g) (hg0 : g ≠ 0) :
    ∃ gr, IsGoodOption gr g ∧ IsRacingOption gr g := by
  obtain ⟨y, hy_mem, hy_race⟩ := exists_mem_rightMoves_race_succ hg hg0
  obtain ⟨gr, hgr_good, hge⟩ := exists_isGoodOption_le_of_mem_rightMoves hg hy_mem
  have h1 : race gr ≤ race y := race_ge_of_ge (hg.of_mem_rightMoves hy_mem)
    (hg.of_mem_rightMoves hgr_good.1) hge
  have h2 : race g ≤ race gr + 1 := race_le_succ_race_of_mem_rightMoves hg hgr_good.1
  exact ⟨gr, hgr_good, hgr_good.1, by omega⟩

theorem exists_isGoodOption_isStallingOption {g : GameForm} (hg : IsLde g) (hg0 : g ≠ 0) :
    ∃ gr, IsGoodOption gr g ∧ IsStallingOption gr g := by
  obtain ⟨y, hy_mem, hy_b⟩ := exists_mem_rightMoves_birthday_succ hg hg0
  obtain ⟨gr, hgr_good, hge⟩ := exists_isGoodOption_le_of_mem_rightMoves hg hy_mem
  have h1 : birthday y ≤ birthday gr :=
    birthday_le_of_ge (hg.of_mem_rightMoves hy_mem) (hg.of_mem_rightMoves hgr_good.1) hge
  refine ⟨gr, hgr_good, hgr_good.1, le_antisymm ?_
    (Order.add_one_le_of_lt (birthday_lt_of_mem_moves hgr_good.1))⟩
  rw [hy_b]
  exact add_le_add_left h1 1

private theorem isRacingOption_of_add {a x ar : GameForm} (ha : IsLde a) (hx : IsLde x)
    (har : ar ∈ moves .right a) (h : IsRacingOption (ar + x) (a + x)) : IsRacingOption ar a := by
  refine ⟨har, ?_⟩
  have h2 := h.2
  rw [race_add ha hx, race_add (ha.of_mem_rightMoves har) hx] at h2
  omega

private theorem isStallingOption_of_add {a x ar : GameForm}
    (har : ar ∈ moves .right a) (h : IsStallingOption (ar + x) (a + x)) :
    IsStallingOption ar a := by
  refine ⟨har, ?_⟩
  have h2 := h.2
  rw [birthday_add, birthday_add, add_right_comm] at h2
  exact add_right_cancel h2

private theorem isGoodPfChain_of_distinguished
    (D : GameForm → GameForm → Prop)
    (hexists : ∀ x : GameForm, IsLde x → x ≠ 0 → ∃ xr, IsGoodOption xr x ∧ D xr x)
    (hrestrict : ∀ a x ar : GameForm, IsLde a → IsLde x → ar ∈ moves .right a →
      D (ar + x) (a + x) → D ar a)
    {S : GameForm → Prop} (hS : ∀ a, S a → IsLdeAtom a)
    (hpf : ∀ a, S a → ∀ ar, IsGoodOption ar a → D ar a → IsPrimeFactorisable ar) :
    ∀ s : Multiset GameForm, (∀ a ∈ s, S a) → IsGoodPfChain s := by
  intro s
  induction hn : Multiset.card s generalizing s with
  | zero =>
    intro _
    rw [Multiset.card_eq_zero.mp hn]
    exact IsGoodPfChain.nil
  | succ n ih =>
    intro hmem
    have hs_lde : ∀ a ∈ s, IsLde a := fun a ha => (hS a (hmem a ha)).1
    have hsum_lde : IsLde s.sum := isLde_sum hs_lde
    have hs0 : s.sum ≠ 0 := by
      intro hc
      have := card_le_race_sum fun a ha => hS a (hmem a ha)
      rw [hc, (lde_race_zero_iff isLde_zero).mpr rfl] at this
      omega
    -- pick a good distinguished option of the whole sum and see which factor it moves in
    obtain ⟨y, hy_good, hy_D⟩ := hexists s.sum hsum_lde hs0
    obtain ⟨a, t, rfl, ar, har, rfl⟩ := exists_eq_add_sum_of_mem_rightMoves_sum hy_good.1
    have ha_lde : IsLde a := hs_lde a (Multiset.mem_cons_self a t)
    have ht_lde : ∀ b ∈ t, IsLde b := fun b hb => hs_lde b (Multiset.mem_cons_of_mem hb)
    have htsum_lde : IsLde t.sum := isLde_sum ht_lde
    have hcons : a + t.sum = (a ::ₘ t).sum := by rw [Multiset.sum_cons]
    refine IsGoodPfChain.cons har (by rw [hcons]; exact hy_good) ?_ ?_
    · refine hpf a (hmem a (Multiset.mem_cons_self a t)) ar
        (isGoodOption_of_add_isGoodOption ha_lde htsum_lde har (by rw [hcons]; exact hy_good))
        (hrestrict a t.sum ar ha_lde htsum_lde har (by rw [hcons]; exact hy_D))
    · exact ih t (by rw [Multiset.card_cons] at hn; omega)
        (fun b hb => hmem b (Multiset.mem_cons_of_mem hb))

/--
If $S \subseteq \mathcal{L}$ is a set of atoms such that every good racing option of every
$G \in S$ is prime-factorisable, then every $S$-factorisation is uniquely factorisable.

This is [Davies (Theorem 7.8 on p. 36)][davies:FactorisationsLeftDead:2024].
-/
theorem uniquelyFactorisable_S_racing {S : GameForm → Prop} (hS : ∀ a, S a → IsLdeAtom a)
    (hpf : ∀ a, S a → ∀ ar, IsGoodOption ar a → IsRacingOption ar a → IsPrimeFactorisable ar)
    {s : Multiset GameForm} (hs : ∀ a ∈ s, S a) : UniquelyFactorisable s.sum := by
  refine uniquelyFactorisable_of_chain
    ⟨fun a ha => hS a (hs a ha), fun _ _ => rfl⟩ ?_
  exact isGoodPfChain_of_distinguished IsRacingOption
    (fun x hx hx0 => exists_isGoodOption_isRacingOption hx hx0)
    (fun a x ar ha hx har h => isRacingOption_of_add ha hx har h) hS hpf s hs

/--
If $S \subseteq \mathcal{L}$ is a set of atoms such that every good stalling option of
every $G \in S$ is prime-factorisable, then every $S$-factorisation is uniquely
factorisable.

This is [Davies (Theorem 7.9 on p. 36)][davies:FactorisationsLeftDead:2024].
-/
theorem uniquelyFactorisable_S_stalling {S : GameForm → Prop} (hS : ∀ a, S a → IsLdeAtom a)
    (hpf : ∀ a, S a → ∀ ar, IsGoodOption ar a → IsStallingOption ar a → IsPrimeFactorisable ar)
    {s : Multiset GameForm} (hs : ∀ a ∈ s, S a) : UniquelyFactorisable s.sum := by
  refine uniquelyFactorisable_of_chain
    ⟨fun a ha => hS a (hs a ha), fun _ _ => rfl⟩ ?_
  exact isGoodPfChain_of_distinguished IsStallingOption
    (fun x hx hx0 => exists_isGoodOption_isStallingOption hx hx0)
    (fun _ _ _ _ _ har h => isStallingOption_of_add har h) hS hpf s hs

/--
If $G$ and $H$ are Left dead ends, where $G$ is uniquely factorisable, and $H$ is
prime-factorisable, then $G + H$ is uniquely factorisable.

This is [Davies (Lemma 7.14 on p. 38)][davies:FactorisationsLeftDead:2024].
-/
theorem uniquelyFactorisable_add_of_isPrimeFactorisable {g h : GameForm} (hg : IsLde g)
    (hh : IsLde h) (hgu : UniquelyFactorisable g) (hpf : IsPrimeFactorisable h) :
    UniquelyFactorisable (g + h) := by
  obtain ⟨u, hu, husum⟩ := hpf
  have hcast : ∀ r : Multiset GameForm, IsFactorisation r (g + h) →
      IsFactorisation r (g + u.sum) := by
    refine fun r hr => ⟨hr.1, hr.2.trans ?_⟩
    exact Form.MisereQuotient.add_misereEQ_add hh.shortDeadEnding hg.shortDeadEnding
      (fun _ _ => rfl) husum.symm
  intro s t hs ht
  obtain ⟨v, w, rfl, hvu, hw⟩ := exists_split_isFactorisation_of_primes hg hu (hcast _ hs)
  obtain ⟨v', w', rfl, hv'u, hw'⟩ := exists_split_isFactorisation_of_primes hg hu (hcast _ ht)
  exact Multiset.Rel.add (Multiset.Rel.trans _ hvu (misereRel_symm hv'u)) (hgu w w' hw hw')

/--
If $G$ is a Left dead end with a good prime-factorisable option $H$, then $G$ is uniquely
factorisable.

This is [Davies (Proposition 7.10 on p. 37)][davies:FactorisationsLeftDead:2024].
-/
theorem uniquelyFactorisable_of_good_pf {g gr : GameForm} (hg : IsLde g)
    (hgo : IsGoodOption gr g) (hpf : IsPrimeFactorisable gr) : UniquelyFactorisable g := by
  obtain ⟨s, hs, hcard⟩ := exists_isFactorisation_card_longestFactorisationLen hg
  have hs_lde : ∀ a ∈ s, IsLde a := fun a ha => (hs.1 a ha).1
  have hsum_lde : IsLde s.sum := isLde_sum hs_lde
  obtain ⟨y, hy_good, hy_eq⟩ := lde_good_option_misereEQ hg hsum_lde hs.2.symm hgo
  obtain ⟨a, t, rfl, ar, har, rfl⟩ := exists_eq_add_sum_of_mem_rightMoves_sum hy_good.1
  have ha_atom : IsLdeAtom a := hs.1 a (Multiset.mem_cons_self a t)
  have ht_lde : ∀ b ∈ t, IsLde b := fun b hb => hs_lde b (Multiset.mem_cons_of_mem hb)
  have har_lde : IsLde ar := ha_atom.1.of_mem_rightMoves har
  -- every remaining factor divides the prime-factorisable option, hence is prime
  have hprime : ∀ b ∈ t, IsLdePrime b := by
    intro b hb
    refine isLdePrime_of_isLdeAtom_dvd (hs.1 b (Multiset.mem_cons_of_mem hb)) hpf ?_
    obtain ⟨t', rfl⟩ := Multiset.exists_cons_of_mem hb
    have ht'_lde : ∀ c ∈ t', IsLde c := fun c hc => ht_lde c (Multiset.mem_cons_of_mem hc)
    refine ⟨ar + t'.sum, har_lde.add (isLde_sum ht'_lde), hy_eq.trans ?_⟩
    rw [Multiset.sum_cons, ← add_assoc, add_comm ar b, add_assoc]
    exact fun _ _ => rfl
  -- so `g ≡ₗ a + t.sum` with `a` an atom and `t.sum` prime-factorisable
  refine UniquelyFactorisable.of_misereEQ
    (uniquelyFactorisable_add_of_isPrimeFactorisable ha_atom.1 (isLde_sum ht_lde)
      ha_atom.uniquelyFactorisable ⟨t, hprime, fun _ _ => rfl⟩) ?_
  refine (hs.2.symm.trans ?_).symm
  rw [Multiset.sum_cons]
  exact fun _ _ => rfl

/--
If $G$ is a Left dead end with a good option $\overline{n}$, then either
$G = \overline{n + 1}$, or else $G$ is an atom.

This is [Davies (Proposition 7.11 on p. 37)][davies:FactorisationsLeftDead:2024].
-/
theorem atom_or_succ_of_good_int {g : GameForm} (hg : IsLde g) {n : ℕ}
    (hgo : IsGoodOption (-(n : GameForm)) g) : (g ≡ₗ -((n + 1 : ℕ) : GameForm)) ∨ IsLdeAtom g := by
  by_cases hatom : IsLdeAtom g
  · exact Or.inr hatom
  refine Or.inl ?_
  obtain ⟨s, hs⟩ := lde_atomic hg
  have hs_lde : ∀ a ∈ s, IsLde a := fun a ha => (hs.1 a ha).1
  have hsum_lde : IsLde s.sum := isLde_sum hs_lde
  obtain ⟨y, hy_good, hy_eq⟩ := lde_good_option_misereEQ hg hsum_lde hs.2.symm hgo
  obtain ⟨a, t, rfl, ar, har, rfl⟩ := exists_eq_add_sum_of_mem_rightMoves_sum hy_good.1
  have ha_atom : IsLdeAtom a := hs.1 a (Multiset.mem_cons_self a t)
  have ht_lde : ∀ b ∈ t, IsLde b := fun b hb => hs_lde b (Multiset.mem_cons_of_mem hb)
  have har_lde : IsLde ar := ha_atom.1.of_mem_rightMoves har
  -- every factor other than `a` is a `1`, because `n` factorises uniquely
  obtain ⟨w, hw⟩ := lde_atomic har_lde
  have hwt : w + t = Multiset.replicate n (-(1 : GameForm)) := by
    refine eq_replicate_of_isFactorisation_neg_intCast ⟨fun b hb => ?_, ?_⟩
    · rcases Multiset.mem_add.mp hb with hb' | hb'
      · exact hw.1 b hb'
      · exact hs.1 b (Multiset.mem_cons_of_mem hb')
    · rw [Multiset.sum_add]
      exact (Form.MisereQuotient.add_misereEQ_add (isLde_sum ht_lde).shortDeadEnding
        har_lde.shortDeadEnding hw.2 (fun _ _ => rfl)).trans hy_eq.symm
  have hall : ∀ b ∈ t, b = -(1 : GameForm) := fun b hb =>
    (Multiset.eq_replicate.mp hwt).2 b (Multiset.mem_add.mpr (Or.inr hb))
  have htrep : t = Multiset.replicate (Multiset.card t) (-(1 : GameForm)) :=
    Multiset.eq_replicate_card.mpr hall
  have htsum : t.sum = -((Multiset.card t : ℕ) : GameForm) := by
    conv_lhs => rw [htrep]
    rw [Multiset.sum_replicate, nsmul_neg_one]
  -- `g ≡ₗ a + m` with `m ≥ 1`, else `g` would be the atom `a`
  have hga : g ≡ₗ (a + -((Multiset.card t : ℕ) : GameForm)) := by
    refine hs.2.symm.trans ?_
    rw [Multiset.sum_cons, htsum]
    exact fun _ _ => rfl
  obtain ⟨m, hm⟩ : ∃ m, Multiset.card t = m + 1 := by
    rcases Nat.eq_zero_or_pos (Multiset.card t) with hc | hc
    · refine absurd (ha_atom.of_misereEQ hg ?_) hatom
      rw [hc, neg_intCast_eq_zero_iff.mpr rfl, add_zero] at hga
      exact hga.symm
    · exact ⟨Multiset.card t - 1, by omega⟩
  rw [hm] at hga
  -- Proposition 4.2: `g ≡ₗ {· | a + (m)}`, so its unique good option pins down `n`
  set X : GameForm := a + -(m : GameForm) with hX
  have hX_lde : IsLde X := ha_atom.1.add (isLde_neg_intCast m)
  have hgX : g ≡ₗ !{(∅ : Set GameForm) | {X}} := by
    refine hga.trans ((?_ : (a + -((m + 1 : ℕ) : GameForm)) ≡ₗ (-(1 : GameForm) + X)).trans
      (neg_one_add_eq_singleton hX_lde))
    rw [hX, show m + 1 = 1 + m from by omega, neg_intCast_add, Nat.cast_one]
    rw [show a + (-(1 : GameForm) + -(m : GameForm))
      = -(1 : GameForm) + (a + -(m : GameForm)) from by ac_rfl]
    exact fun _ _ => rfl
  obtain ⟨z, hz_good, hz_eq⟩ := lde_good_option_misereEQ hg (isLde_singletonRight hX_lde) hgX hgo
  have hzX : z = X := by
    have := hz_good.1
    rw [rightMoves_singletonRight] at this
    exact this
  rw [hzX] at hz_eq
  -- `n ≡ₗ a + m` factorises `n`, so `a = 1` and `m + 1 = n`
  have hfac2 : a ::ₘ Multiset.replicate m (-(1 : GameForm))
      = Multiset.replicate n (-(1 : GameForm)) := by
    refine eq_replicate_of_isFactorisation_neg_intCast ⟨fun b hb => ?_, ?_⟩
    · rcases Multiset.mem_cons.mp hb with rfl | hb'
      · exact ha_atom
      · rw [Multiset.eq_of_mem_replicate hb']
        exact isLdeAtom_neg_one
    · rw [Multiset.sum_cons, Multiset.sum_replicate, nsmul_neg_one]
      exact hz_eq.symm
  have hcard2 : m + 1 = n := by
    have := congrArg Multiset.card hfac2
    simpa using this
  have ha1 : a = -(1 : GameForm) :=
    (Multiset.eq_replicate.mp hfac2).2 a (Multiset.mem_cons_self a _)
  refine hga.trans ?_
  rw [ha1, ← Nat.cast_one (R := GameForm), ← neg_intCast_add,
    show 1 + (m + 1) = n + 1 from by omega]
  exact fun _ _ => rfl

/-- This is [Davies (Question 7.12 on p. 38)][davies:FactorisationsLeftDead:2024]. -/
def GoodPrimeFactorisableQuestion : Prop :=
  ∀ g gr : GameForm.{u}, IsLde g → IsGoodOption gr g → IsPrimeFactorisable gr →
    IsPrimeFactorisable g ∨ IsLdeAtom g

/--
If $G$ is a Left dead end that is an atom with a good prime-factorisable option, then $G$
is a strong atom.

This is [Davies (Lemma 7.15 on p. 38)][davies:FactorisationsLeftDead:2024].
-/
theorem strongAtom_of_atom_good_pf {g gr : GameForm} (hg : IsLdeAtom g)
    (hgo : IsGoodOption gr g) (hpf : IsPrimeFactorisable gr) (n : ℕ) :
    UniquelyFactorisable (n • g) := by
  have hchain : ∀ k : ℕ, IsGoodPfChain (Multiset.replicate k g) := by
    intro k
    induction k with
    | zero =>
      rw [Multiset.replicate_zero]
      exact IsGoodPfChain.nil
    | succ k ih =>
      rw [Multiset.replicate_succ]
      refine IsGoodPfChain.cons hgo.1 ?_ hpf ih
      rw [Multiset.sum_replicate, ← succ_nsmul']
      exact (isGoodOption_add_nsmul_iff hg.1 hgo.1 k).mpr hgo
  refine uniquelyFactorisable_of_chain ?_ (hchain n)
  exact ⟨fun a ha => by rwa [Multiset.eq_of_mem_replicate ha],
    by rw [Multiset.sum_replicate]; exact fun _ _ => rfl⟩

/--
If $G$ is a Left dead end with a good prime-factorisable option, then $n \cdot G$ is
uniquely factorisable for all $n$.

This is [Davies (Theorem 7.16 on p. 39)][davies:FactorisationsLeftDead:2024].
-/
theorem nsmul_uniquelyFactorisable_of_good_pf {g gr : GameForm} (hg : IsLde g)
    (hgo : IsGoodOption gr g) (hpf : IsPrimeFactorisable gr) (n : ℕ) :
    UniquelyFactorisable (n • g) := by
  obtain ⟨s, hs⟩ := lde_atomic hg
  have hs_lde : ∀ a ∈ s, IsLde a := fun a ha => (hs.1 a ha).1
  have hsum_lde : IsLde s.sum := isLde_sum hs_lde
  obtain ⟨y, hy_good, hy_eq⟩ := lde_good_option_misereEQ hg hsum_lde hs.2.symm hgo
  obtain ⟨a, t, rfl, ar, har, rfl⟩ := exists_eq_add_sum_of_mem_rightMoves_sum hy_good.1
  have ha_atom : IsLdeAtom a := hs.1 a (Multiset.mem_cons_self a t)
  have ht_lde : ∀ b ∈ t, IsLde b := fun b hb => hs_lde b (Multiset.mem_cons_of_mem hb)
  have htsum_lde : IsLde t.sum := isLde_sum ht_lde
  have har_lde : IsLde ar := ha_atom.1.of_mem_rightMoves har
  -- `ar` divides the prime-factorisable option, hence is prime-factorisable itself
  have har_pf : IsPrimeFactorisable ar :=
    isPrimeFactorisable_of_dvd har_lde hpf ⟨t.sum, htsum_lde, hy_eq⟩
  -- and each remaining factor is an atom dividing it, hence prime
  have hprime : ∀ b ∈ t, IsLdePrime b := by
    intro b hb
    refine isLdePrime_of_isLdeAtom_dvd (hs.1 b (Multiset.mem_cons_of_mem hb)) hpf ?_
    obtain ⟨t', rfl⟩ := Multiset.exists_cons_of_mem hb
    have ht'_lde : ∀ c ∈ t', IsLde c := fun c hc => ht_lde c (Multiset.mem_cons_of_mem hc)
    refine ⟨ar + t'.sum, har_lde.add (isLde_sum ht'_lde), hy_eq.trans ?_⟩
    rw [Multiset.sum_cons, ← add_assoc, add_comm ar b, add_assoc]
    exact fun _ _ => rfl
  -- Lemma 7.7 makes `ar` good on the component `a`, so `a` is a strong atom (Lemma 7.15)
  have hgood_a : IsGoodOption ar a := by
    refine isGoodOption_of_add_isGoodOption ha_atom.1 htsum_lde har ?_
    have e : a + t.sum = (a ::ₘ t).sum := by rw [Multiset.sum_cons]
    rw [e]
    exact hy_good
  have hna : UniquelyFactorisable (n • a) :=
    strongAtom_of_atom_good_pf ha_atom hgood_a har_pf n
  -- `n • g ≡ₗ n • a + n • t.sum`, an atom multiple plus a prime-factorisable game
  refine UniquelyFactorisable.of_misereEQ
    (uniquelyFactorisable_add_of_isPrimeFactorisable (isLde_nsmul ha_atom.1 n)
      (isLde_nsmul htsum_lde n) hna
      (IsPrimeFactorisable.nsmul htsum_lde ⟨t, hprime, fun _ _ => rfl⟩ n)) ?_
  rw [← nsmul_add]
  refine nsmul_misereEQ_nsmul (ha_atom.1.add htsum_lde) hg ?_ n
  refine (show (a + t.sum) ≡ₗ (a ::ₘ t).sum by rw [Multiset.sum_cons]; exact fun _ _ => rfl).trans
    hs.2

/-! ## The central conjecture -/

/--
A minimal counterexample to unique factorisation has more than one good option.

This is part of the Section 8 discussion in
[Davies (p. 39)][davies:FactorisationsLeftDead:2024].
-/
theorem counterexample_has_multi_good {g : GameForm} (hg : IsLde g)
    (hnu : ¬ UniquelyFactorisable g)
    (hmin : ∀ g', IsLde g' → birthday g' < birthday g → UniquelyFactorisable g') :
    ∃ a b, IsGoodOption a g ∧ IsGoodOption b g ∧ ¬ (a ≡ₗ b) := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hnu (uniquelyFactorisable_of_longestLen_le_one isLde_zero
      (by rw [longestFactorisationLen_zero]; exact Nat.zero_le 1))
  rcases hasUniqueGoodOption_or_multi hg hg0 with ⟨gr, hgr_good, hgr_uniq⟩ | hmulti
  · refine absurd ?_ hnu
    have hgr_lde : IsLde gr := hg.of_mem_rightMoves hgr_good.1
    have heq : g ≡ₗ (-(1 : GameForm) + gr) :=
      (unique_good_option_iff hg hgr_lde).mp ⟨gr, hgr_good, fun _ _ => rfl, hgr_uniq⟩
    have hpf : IsPrimeFactorisable (-(1 : GameForm)) :=
      ⟨{-(1 : GameForm)}, by simpa using neg_one_prime,
        by rw [Multiset.sum_singleton]; exact fun _ _ => rfl⟩
    refine (uniquelyFactorisable_add_of_isPrimeFactorisable hgr_lde (isLde_neg_one)
      (hmin gr hgr_lde (birthday_lt_of_mem_moves hgr_good.1)) hpf).of_misereEQ ?_
    rw [add_comm]
    exact heq.symm
  · exact hmulti

/--
Every good option of a minimal counterexample to unique factorisation is a molecule.

This is part of the Section 8 discussion in
[Davies (p. 39)][davies:FactorisationsLeftDead:2024].
-/
theorem counterexample_good_options_molecular {g : GameForm} (hg : IsLde g)
    (hnu : ¬ UniquelyFactorisable g) {gr : GameForm} (hgo : IsGoodOption gr g) :
    ¬ IsLdeAtom gr := by
  intro hatom
  exact hnu (uniquelyFactorisable_of_good_atom hg hatom hgo)

private theorem ldeDvd_of_mem_isFactorisation {x g : GameForm} {s : Multiset GameForm}
    (hs : IsFactorisation s g) (hx : x ∈ s) : LdeDvd x g := by
  obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem hx
  refine ⟨s'.sum, isLde_sum fun c hc => (hs.1 c (Multiset.mem_cons_of_mem hc)).1, ?_⟩
  rw [← Multiset.sum_cons]
  exact hs.2.symm

private theorem birthday_le_of_mem_isFactorisation {x p : GameForm} (hx : IsLde x)
    {v : Multiset GameForm} (hv : IsFactorisation v x) (hp : p ∈ v) :
    birthday p ≤ birthday x := by
  obtain ⟨v', rfl⟩ := Multiset.exists_cons_of_mem hp
  have hp_lde : IsLde p := (hv.1 p (Multiset.mem_cons_self ..)).1
  have hv'_lde : IsLde v'.sum :=
    isLde_sum fun c hc => (hv.1 c (Multiset.mem_cons_of_mem hc)).1
  have heq : (p + v'.sum) ≡ₗ x := by rw [← Multiset.sum_cons]; exact hv.2
  rw [← birthday_eq_of_misereEQ (hp_lde.add hv'_lde) hx heq, birthday_add]
  exact le_add_of_nonneg_right (NatOrdinal.zero_le _)

/--
Two factorisations of a minimal counterexample to unique factorisation share no atom.

This is part of the Section 8 discussion in
[Davies (p. 39)][davies:FactorisationsLeftDead:2024].
-/
theorem counterexample_factorisations_disjoint {g : GameForm} (hg : IsLde g)
    (hmin : ∀ g', IsLde g' → birthday g' < birthday g → UniquelyFactorisable g')
    {s t : Multiset GameForm} (hs : IsFactorisation s g) (ht : IsFactorisation t g)
    (hst : ¬ Multiset.Rel (· ≡ₗ ·) s t) {x y : GameForm} (hx : x ∈ s) (hy : y ∈ t) :
    ¬ (x ≡ₗ y) := by
  intro hxy
  obtain ⟨s₀, rfl⟩ := Multiset.exists_cons_of_mem hx
  obtain ⟨t₀, rfl⟩ := Multiset.exists_cons_of_mem hy
  have hx_atom : IsLdeAtom x := hs.1 x (Multiset.mem_cons_self ..)
  have hy_lde : IsLde y := (ht.1 y (Multiset.mem_cons_self ..)).1
  have hs₀ : ∀ a ∈ s₀, IsLdeAtom a := fun a ha => hs.1 a (Multiset.mem_cons_of_mem ha)
  have ht₀ : ∀ a ∈ t₀, IsLdeAtom a := fun a ha => ht.1 a (Multiset.mem_cons_of_mem ha)
  have hs₀_lde : IsLde s₀.sum := isLde_sum fun a ha => (hs₀ a ha).1
  have ht₀_lde : IsLde t₀.sum := isLde_sum fun a ha => (ht₀ a ha).1
  have hgx : g ≡ₗ (x + s₀.sum) := by rw [← Multiset.sum_cons]; exact hs.2.symm
  have hgy : g ≡ₗ (y + t₀.sum) := by rw [← Multiset.sum_cons]; exact ht.2.symm
  -- cancel the shared atom `x ≡ₗ y`
  have hcancel : s₀.sum ≡ₗ t₀.sum := by
    refine lde_cancellative hs₀_lde ht₀_lde hx_atom.1 ?_
    rw [add_comm s₀.sum x, add_comm t₀.sum x]
    refine hgx.symm.trans (hgy.trans ?_)
    exact Form.MisereQuotient.add_misereEQ_add ht₀_lde.shortDeadEnding hx_atom.1.shortDeadEnding
      hxy.symm (fun _ _ => rfl)
  -- the cancelled game is strictly younger, hence uniquely factorisable
  have hb : birthday s₀.sum < birthday g := by
    rw [birthday_eq_of_misereEQ hg (hx_atom.1.add hs₀_lde) hgx, birthday_add]
    exact lt_add_of_pos_left _ (birthday_pos_of_ne_zero hx_atom.1 hx_atom.2.1)
  exact hst (Multiset.Rel.cons hxy
    (hmin _ hs₀_lde hb s₀ t₀ ⟨hs₀, fun _ _ => rfl⟩ ⟨ht₀, hcancel.symm⟩))

private theorem two_le_card_of_class_disjoint {g A B : GameForm} (hg : IsLde g) (hg0 : g ≠ 0)
    {s t : Multiset GameForm} (hs : IsFactorisation s g) (ht : IsFactorisation t g)
    (hsA : ∀ x ∈ s, x ≡ₗ A) (htB : ∀ y ∈ t, y ≡ₗ B) (hAB : ¬ (A ≡ₗ B)) :
    2 ≤ Multiset.card s := by
  by_contra hc
  push_neg at hc
  have h1 : 0 < Multiset.card s := (card_pos_iff_of_isFactorisation hg hs).mpr hg0
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp (by omega : Multiset.card s = 1)
  have ha_eq : a ≡ₗ g := by rw [← Multiset.sum_singleton (a := a)]; exact hs.2
  have hga : IsLdeAtom g :=
    (hs.1 a (Multiset.mem_singleton_self a)).of_misereEQ hg ha_eq
  have h2 : Multiset.card t ≤ 1 := by
    have := card_le_longestFactorisationLen hg ht
    rwa [longestFactorisationLen_isLdeAtom hga] at this
  have h3 : 0 < Multiset.card t := (card_pos_iff_of_isFactorisation hg ht).mpr hg0
  obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp (by omega : Multiset.card t = 1)
  have hb_eq : b ≡ₗ g := by rw [← Multiset.sum_singleton (a := b)]; exact ht.2
  exact hAB (((hsA a (Multiset.mem_singleton_self a)).symm.trans
    (ha_eq.trans hb_eq.symm)).trans (htB b (Multiset.mem_singleton_self b)))

private theorem birthday_lt_of_class_disjoint {g A B : GameForm} (hg : IsLde g) (hg0 : g ≠ 0)
    (hmin : ∀ g', IsLde g' → birthday g' < birthday g → UniquelyFactorisable g')
    (hA : IsLde A) (hB : IsLde B)
    {s t : Multiset GameForm} (hs : IsFactorisation s g) (ht : IsFactorisation t g)
    (hsA : ∀ x ∈ s, x ≡ₗ A) (htB : ∀ y ∈ t, y ≡ₗ B) (hAB : ¬ (A ≡ₗ B)) :
    birthday A < birthday B := by
  have hcards : 2 ≤ Multiset.card s := two_le_card_of_class_disjoint hg hg0 hs ht hsA htB hAB
  have hs_lde : IsLde s.sum := isLde_sum fun a ha => (hs.1 a ha).1
  have ht_lde : IsLde t.sum := isLde_sum fun a ha => (ht.1 a ha).1
  obtain ⟨w, hw⟩ := hg.rightMoves_nonempty hg0
  obtain ⟨gr, hgr_good, -⟩ := exists_isGoodOption_le_of_mem_rightMoves hg hw
  obtain ⟨y, hy_good, hgry⟩ := lde_good_option_misereEQ hg hs_lde hs.2.symm hgr_good
  obtain ⟨z, hz_good, hgrz⟩ := lde_good_option_misereEQ hg ht_lde ht.2.symm hgr_good
  obtain ⟨a, s', hs_eq, ar, har, rfl⟩ := exists_eq_add_sum_of_mem_rightMoves_sum hy_good.1
  obtain ⟨b, t', ht_eq, br, hbr, rfl⟩ := exists_eq_add_sum_of_mem_rightMoves_sum hz_good.1
  subst hs_eq
  subst ht_eq
  have ha_lde : IsLde a := (hs.1 a (Multiset.mem_cons_self ..)).1
  have hb_lde : IsLde b := (ht.1 b (Multiset.mem_cons_self ..)).1
  have har_lde : IsLde ar := ha_lde.of_mem_rightMoves har
  have hbr_lde : IsLde br := hb_lde.of_mem_rightMoves hbr
  have hs'_lde : IsLde s'.sum :=
    isLde_sum fun c hc => (hs.1 c (Multiset.mem_cons_of_mem hc)).1
  have ht'_lde : IsLde t'.sum :=
    isLde_sum fun c hc => (ht.1 c (Multiset.mem_cons_of_mem hc)).1
  obtain ⟨u, hu⟩ := lde_atomic har_lde
  obtain ⟨v, hv⟩ := lde_atomic hbr_lde
  -- both decompositions factorise the good option `gr`, which minimality makes unique
  have hufgr : UniquelyFactorisable gr :=
    hmin gr (hg.of_mem_rightMoves hgr_good.1) (birthday_lt_of_mem_moves hgr_good.1)
  have hfac1 : IsFactorisation (u + s') gr := by
    refine ⟨fun c hc => (Multiset.mem_add.mp hc).elim (hu.1 c)
      fun h => hs.1 c (Multiset.mem_cons_of_mem h), ?_⟩
    rw [Multiset.sum_add]
    refine MisereEQ.trans ?_ hgry.symm
    exact Form.MisereQuotient.add_misereEQ_add hs'_lde.shortDeadEnding har_lde.shortDeadEnding
      hu.2 (fun _ _ => rfl)
  have hfac2 : IsFactorisation (v + t') gr := by
    refine ⟨fun c hc => (Multiset.mem_add.mp hc).elim (hv.1 c)
      fun h => ht.1 c (Multiset.mem_cons_of_mem h), ?_⟩
    rw [Multiset.sum_add]
    refine MisereEQ.trans ?_ hgrz.symm
    exact Form.MisereQuotient.add_misereEQ_add ht'_lde.shortDeadEnding hbr_lde.shortDeadEnding
      hv.2 (fun _ _ => rfl)
  have hrel := hufgr _ _ hfac1 hfac2
  -- the leftover `A`-atom must be matched inside the factorisation of `br`
  obtain ⟨e, he⟩ : ∃ e, e ∈ s' := by
    rw [Multiset.card_cons] at hcards
    exact Multiset.exists_mem_of_ne_zero
      (fun hc => by rw [hc] at hcards; simp at hcards)
  obtain ⟨p, hp_mem, hep⟩ :=
    Multiset.exists_mem_of_rel_of_mem hrel (Multiset.mem_add.mpr (Or.inr he))
  have hp_v : p ∈ v := by
    rcases Multiset.mem_add.mp hp_mem with h | h
    · exact h
    · exact absurd (((hsA e (Multiset.mem_cons_of_mem he)).symm.trans hep).trans
        (htB p (Multiset.mem_cons_of_mem h))) hAB
  calc birthday A
      = birthday p := birthday_eq_of_misereEQ hA (hv.1 p hp_v).1
        ((hsA e (Multiset.mem_cons_of_mem he)).symm.trans hep)
    _ ≤ birthday br := birthday_le_of_mem_isFactorisation hbr_lde hv hp_v
    _ < birthday b := birthday_lt_of_mem_moves hbr
    _ = birthday B := birthday_eq_of_misereEQ hb_lde hB
        (htB b (Multiset.mem_cons_self ..))

/--
A minimal counterexample to unique factorisation has at least three atoms that are
factors.

This is part of the Section 8 discussion in
[Davies (p. 39)][davies:FactorisationsLeftDead:2024].
-/
theorem counterexample_has_three_atoms {g : GameForm} (hg : IsLde g)
    (hnu : ¬ UniquelyFactorisable g)
    (hmin : ∀ g', IsLde g' → birthday g' < birthday g → UniquelyFactorisable g') :
    ∃ a b c, IsLdeAtom a ∧ IsLdeAtom b ∧ IsLdeAtom c ∧
      LdeDvd a g ∧ LdeDvd b g ∧ LdeDvd c g ∧
      ¬ (a ≡ₗ b) ∧ ¬ (a ≡ₗ c) ∧ ¬ (b ≡ₗ c) := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hnu (uniquelyFactorisable_of_longestLen_le_one isLde_zero
      (by rw [longestFactorisationLen_zero]; exact Nat.zero_le 1))
  obtain ⟨s, t, hs, ht, hst⟩ : ∃ s t, IsFactorisation s g ∧ IsFactorisation t g ∧
      ¬ Multiset.Rel (· ≡ₗ ·) s t := by
    by_contra hc
    push_neg at hc
    exact hnu fun s t hsf htf => hc s t hsf htf
  have hdisj : ∀ x ∈ s, ∀ y ∈ t, ¬ (x ≡ₗ y) :=
    fun _ hx _ hy => counterexample_factorisations_disjoint hg hmin hs ht hst hx hy
  obtain ⟨A, hA⟩ := Multiset.exists_mem_of_ne_zero (s := s)
    (fun hc => by
      have := (card_pos_iff_of_isFactorisation hg hs).mpr hg0
      rw [hc] at this; simp at this)
  obtain ⟨B, hB⟩ := Multiset.exists_mem_of_ne_zero (s := t)
    (fun hc => by
      have := (card_pos_iff_of_isFactorisation hg ht).mpr hg0
      rw [hc] at this; simp at this)
  have hAB : ¬ (A ≡ₗ B) := hdisj A hA B hB
  obtain ⟨C, hC, hCA, hCB⟩ : ∃ C ∈ s + t, ¬ (C ≡ₗ A) ∧ ¬ (C ≡ₗ B) := by
    by_contra hc
    push_neg at hc
    have hsA : ∀ x ∈ s, x ≡ₗ A := by
      intro x hx
      by_cases hxA : x ≡ₗ A
      · exact hxA
      · exact absurd (hc x (Multiset.mem_add.mpr (Or.inl hx)) hxA) (hdisj x hx B hB)
    have htB : ∀ y ∈ t, y ≡ₗ B := fun y hy =>
      hc y (Multiset.mem_add.mpr (Or.inr hy)) fun h => hdisj A hA y hy h.symm
    have h1 := birthday_lt_of_class_disjoint hg hg0 hmin (hs.1 A hA).1 (ht.1 B hB).1
      hs ht hsA htB hAB
    have h2 := birthday_lt_of_class_disjoint hg hg0 hmin (ht.1 B hB).1 (hs.1 A hA).1
      ht hs htB hsA (fun h => hAB h.symm)
    exact (h1.trans h2).false
  refine ⟨A, B, C, hs.1 A hA, ht.1 B hB,
    (Multiset.mem_add.mp hC).elim (hs.1 C) (ht.1 C),
    ldeDvd_of_mem_isFactorisation hs hA, ldeDvd_of_mem_isFactorisation ht hB,
    (Multiset.mem_add.mp hC).elim (ldeDvd_of_mem_isFactorisation hs)
      (ldeDvd_of_mem_isFactorisation ht),
    hAB, fun h => hCA h.symm, fun h => hCB h.symm⟩

/-- This is [Davies (Open problem 8.1 on p. 39)][davies:FactorisationsLeftDead:2024]. -/
def LdeUniquelyFactorisableConjecture : Prop :=
  ∀ g : GameForm.{u}, IsLde g → UniquelyFactorisable g

/-- This is [Davies (Open problem 8.2 on p. 41)][davies:FactorisationsLeftDead:2024]. -/
def atomsBornBy (n : ℕ) : Set GameForm := {g | IsLdeAtom g ∧ birthday g ≤ n}

/-- This is [Davies (Open problem 8.2 on p. 41)][davies:FactorisationsLeftDead:2024]. -/
def moleculesBornBy (n : ℕ) : Set GameForm := {g | IsMolecule g ∧ birthday g ≤ n}

/-- This is [Davies (Open problem 8.2 on p. 41)][davies:FactorisationsLeftDead:2024]. -/
def atomsWithTerminalLengths (S : Set ℕ) : Set GameForm :=
  {g | IsLdeAtom g ∧ terminalLengths g = S}

/-- This is [Davies (Open problem 8.2 on p. 41)][davies:FactorisationsLeftDead:2024]. -/
def moleculesWithTerminalLengths (S : Set ℕ) : Set GameForm :=
  {g | IsMolecule g ∧ terminalLengths g = S}

end GameForm.LeftDeadEnd
