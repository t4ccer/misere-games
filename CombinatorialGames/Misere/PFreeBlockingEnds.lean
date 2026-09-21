/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.PFreeBlocking

/-!
# Ends of $\operatorname{pf}(\mathcal{U})$ are integers

For a universe `U` carrying the hypotheses of `misereGE_iff_promain` (in particular
`ShortBlocking` and `ShortDeadEnding`), every end of $\operatorname{pf}(\mathcal{U})$ is
equivalent modulo $\operatorname{pf}(\mathcal{U})$ to an integer. This is the blocking analogue
of `isEnd_exists_intCast_misereEQ`.

Throughout, larger integers are smaller games: `a ≤ b` in `ℤ` gives `b ≥m pf(U) a`.

The key step is `misereGE_intCast_or_exists_leftMove_of_not_succ_misereGE`: for every
`g ∈ pf(U)` and every integer `n ≤ 0`, if `n + 1 ≱ g` then `g ≥ n` or some Left option of `g`
is `≥ n - 1`. Applied to a Left end `g` at the largest `n ≤ 0` with `n ≥ g`, it gives `g = n`.

The main results are
* `isEnd_exists_intCast_misereEQ'`
* `isEnd_left_exists_intCast_misereEQ'`
* `isEnd_right_exists_intCast_misereEQ'`
-/

public section

universe u

open Form
open Form.Misere.Outcome
open GameForm
open PFree

namespace PFree

/--
Sufficiency half of the comparison of `g` with a negative integer `n`: it is enough that every
Right option of `g` is `≥ n + 1` or has a Left option `≥ n`.
-/
theorem misereGE_intCast_of_forall_rightMoves
    {U : GameForm → Prop} [ShortUniverse U] [HasInt U] [Blocking U]
    {g : GameForm} {n : ℤ} (h_n : n ≤ -1)
    (h_g : PFreeSubset U g) (h_not_isEnd : ¬ IsEnd .right g) (h_out : MisereOutcome g ≠ .R)
    (h_moves : ∀ gr ∈ moves .right g,
      gr ≥m (PFreeSubset U) ((n + 1 : ℤ) : GameForm) ∨
        ∃ grl ∈ moves .left gr, grl ≥m (PFreeSubset U) ((n : ℤ) : GameForm)) :
    g ≥m (PFreeSubset U) ((n : ℤ) : GameForm) := by
  refine PFreeBlocking.misereGE_of_maintenance_proviso h_g.isPFree (isPFree_intCast n)
    ?_ ?_ ?_ ?_
  · intro gr h_gr
    rw [rightMoves_intCast_of_neg (by omega)]
    rcases h_moves gr h_gr with h_ge | ⟨grl, h_grl, h_ge⟩
    · exact Or.inl ⟨_, Set.mem_singleton _, h_ge⟩
    · exact Or.inr ⟨grl, h_grl, h_ge⟩
  · intro hl h_hl
    exact absurd h_hl (not_mem_moves_of_isEnd (isEnd_left_intCast_iff.mpr (by omega)))
  · intro h_end
    exact absurd h_end h_not_isEnd
  · intro _
    exact h_out

/--
If $\operatorname{o}(G) = \mathscr{L}$ then $G \ge \overline{1}$.
-/
theorem misereGE_neg_one_of_misereOutcome_L
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g : GameForm} (h_g : PFreeSubset U g)
    (h_out : MisereOutcome g = .L) :
    g ≥m (PFreeSubset U) ((-1 : ℤ) : GameForm) := by
  have h_not_win := (misereOutcome_L_iff_winsGoingFirst.mp h_out).right
  have h_not_isEnd : ¬ IsEnd .right g := fun h_end => h_not_win (winsGoingFirst_of_isEnd h_end)
  rw [not_winsGoingFirst_iff] at h_not_win
  refine misereGE_intCast_of_forall_rightMoves le_rfl h_g h_not_isEnd (by rw [h_out]; decide) ?_
  intro gr h_gr
  have h_gr_mem := Hereditary.of_mem_moves h_g h_gr
  have h_gr_win := h_not_win.right gr h_gr
  rw [Player.neg_right, winsGoingFirst_iff] at h_gr_win
  rw [show (-1 + 1 : ℤ) = 0 by omega, Form.intCast_zero]
  rcases h_gr_win with h_end | ⟨grl, h_grl, h_grl_not_win⟩
  · exact Or.inl (Blocking.isEnd_left_misereGE_zero h_gr_mem (isEndLike_iff_isEnd.mp h_end))
  · right
    refine ⟨grl, h_grl, ?_⟩
    have h_grl_mem := Hereditary.of_mem_moves h_gr_mem h_grl
    rw [Player.neg_left] at h_grl_not_win
    exact misereGE_neg_one_of_misereOutcome_L h_grl_mem
      (misereOutcome_of_not_winsGoingFirst h_grl_mem.isPFree h_grl_not_win)
termination_by g
decreasing_by form_wf

/--
Necessity half of the comparison of a negative integer `n` with `g`: if `n ≥ g` and `g` is not a
Right end, then some Right option of `g` is `≤ n + 1`.
-/
theorem exists_rightMove_of_intCast_misereGE
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g : GameForm} {n : ℤ} (h_n : n ≤ -1)
    (h_g : PFreeSubset U g) (h_not_isEnd : ¬ IsEnd .right g)
    (h_ge : ((n : ℤ) : GameForm) ≥m (PFreeSubset U) g) :
    ∃ gr ∈ moves .right g, ((n + 1 : ℤ) : GameForm) ≥m (PFreeSubset U) gr := by
  have h_n_left : IsEnd .left ((n : ℤ) : GameForm) := isEnd_left_intCast_iff.mpr (by omega)
  have h_n_not_right : ¬ IsEnd .right ((n : ℤ) : GameForm) :=
    isEnd_right_intCast_iff.not.mpr (by omega)
  rw [misereGE_iff_promain_not_isEnd_right_right (HasInt.has_int n) h_g h_n_left h_n_not_right
    h_not_isEnd] at h_ge
  obtain ⟨h_mr, -, -, -⟩ := h_ge
  have h_mem : ((n + 1 : ℤ) : GameForm) ∈
      moves .right (!{{(-1 : GameForm)} | (moves .right ((n : ℤ) : GameForm))} : GameForm) := by
    rw [rightMoves_ofSets, rightMoves_intCast_of_neg (by omega)]
    exact Set.mem_singleton _
  rcases h_mr _ h_mem with ⟨gr, h_gr, h_ge⟩ | ⟨grl, h_grl, -⟩
  · exact ⟨gr, h_gr, h_ge⟩
  · exact absurd h_grl (not_mem_moves_of_isEnd (isEnd_left_intCast_iff.mpr (by omega)))

/--
Unwinding `n ≱ g` for an integer `n ≤ 0`: either no Right option of `g` is `≤ n + 1`, or some
Left option `gl` of `g` is not `≤ -1` and has no Right option `≤ n`.
-/
theorem not_intCast_misereGE_cases
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g : GameForm} {n : ℤ} (h_n : n ≤ 0)
    (h_g : PFreeSubset U g) (h_not_ge : ¬ ((n : ℤ) : GameForm) ≥m (PFreeSubset U) g) :
    (∀ gr ∈ moves .right g, ¬ ((n + 1 : ℤ) : GameForm) ≥m (PFreeSubset U) gr) ∨
      ∃ gl ∈ moves .left g, ¬ ((-1 : ℤ) : GameForm) ≥m (PFreeSubset U) gl ∧
        ∀ glr ∈ moves .right gl, ¬ ((n : ℤ) : GameForm) ≥m (PFreeSubset U) glr := by
  by_contra h_contra
  push_neg at h_contra
  obtain ⟨⟨gr, h_gr, h_gr_ge⟩, h_left⟩ := h_contra
  apply h_not_ge
  rcases h_n.lt_or_eq with h_neg | h_zero
  · have h_n1 : n ≤ -1 := by omega
    have h_n_mem : PFreeSubset U ((n : ℤ) : GameForm) := HasInt.has_int n
    have h_n_left : IsEnd .left ((n : ℤ) : GameForm) := isEnd_left_intCast_iff.mpr h_n
    have h_n_not_right : ¬ IsEnd .right ((n : ℤ) : GameForm) :=
      isEnd_right_intCast_iff.not.mpr (by omega)
    have h_eq := Blocking.reduction_plug_end_not_isEnd_right h_n_mem h_n_left h_n_not_right
    rw [misereGE_rw_left_iff h_eq]
    refine PFreeBlocking.misereGE_of_maintenance_proviso
      (Blocking.pluggedLeft_mem h_n_mem h_n_not_right).isPFree h_g.isPFree ?_ ?_ ?_ ?_
    · intro x h_x
      rw [rightMoves_ofSets, rightMoves_intCast_of_neg (by omega), Set.mem_singleton_iff] at h_x
      subst h_x
      exact Or.inl ⟨gr, h_gr, h_gr_ge⟩
    · intro hl h_hl
      by_cases h_ge : ((-1 : ℤ) : GameForm) ≥m (PFreeSubset U) hl
      · left
        refine ⟨(-1 : GameForm), ?_, ?_⟩
        · rw [leftMoves_ofSets]
          exact Set.mem_singleton _
        · rwa [Form.intCast_neg, Form.intCast_one] at h_ge
      · obtain ⟨hlr, h_hlr, h_hlr_ge⟩ := h_left hl h_hl h_ge
        exact Or.inr ⟨hlr, h_hlr, (misereGE_rw_left_iff h_eq).mp h_hlr_ge⟩
    · intro h_end
      rw [isEnd_def, rightMoves_ofSets, rightMoves_intCast_of_neg (by omega)] at h_end
      exact absurd h_end (Set.singleton_ne_empty _)
    · intro _ h_R
      rw [← IntegerInvertible.misereOutcome_eq_of_misereEQ h_eq, misereOutcome_R_intCast_iff] at h_R
      omega
  · subst h_zero
    rw [zero_add, Form.intCast_one] at h_gr_ge
    simp only [Form.intCast_zero, Form.intCast_neg, Form.intCast_one] at h_left ⊢
    cases h_out : MisereOutcome g
    · exfalso
      have h_not_win := (misereOutcome_L_iff_winsGoingFirst.mp h_out).right
      rw [not_winsGoingFirst_iff] at h_not_win
      have h_gr_win := h_not_win.right gr h_gr
      rw [Player.neg_right] at h_gr_win
      exact (misereOutcome_R_iff_winsGoingFirst.mp
        (misereOutcome_R_of_one_misereGE h_gr_ge)).right h_gr_win
    · have h_win := (misereOutcome_N_iff_winsGoingFirst.mp h_out).left
      have h_eq := misereEQ_dominated_not_isEnd_right h_g h_win
      rw [misereGE_rw_right_iff h_eq]
      refine PFreeBlocking.misereGE_of_maintenance_proviso isPFree_zero
        (isPFree_dominated_not_isEnd_right h_g h_win) ?_ ?_ ?_ ?_
      · intro x h_x
        rw [moves_zero] at h_x
        exact absurd h_x (Set.notMem_empty _)
      · intro hl h_hl
        rw [leftMoves_ofSets, Set.mem_setOf_eq] at h_hl
        obtain ⟨h_hl_mem, h_hl_not_isEnd⟩ := h_hl
        have h_hl := Hereditary.of_mem_moves h_g h_hl_mem
        right
        by_cases h_ge : (-1 : GameForm) ≥m (PFreeSubset U) hl
        · have h_ge' : ((-1 : ℤ) : GameForm) ≥m (PFreeSubset U) hl := by
            rwa [Form.intCast_neg, Form.intCast_one]
          obtain ⟨hlr, h_hlr, h_hlr_ge⟩ :=
            exists_rightMove_of_intCast_misereGE le_rfl h_hl h_hl_not_isEnd h_ge'
          refine ⟨hlr, h_hlr, ?_⟩
          rwa [show (-1 + 1 : ℤ) = 0 by omega, Form.intCast_zero] at h_hlr_ge
        · exact h_left hl h_hl_mem h_ge
      · intro _
        rw [← IntegerInvertible.misereOutcome_eq_of_misereEQ h_eq, h_out]
        decide
      · intro _
        rw [misereOutcome_zero_N]
        decide
    · exact absurd h_out (misereOutcome_ne_P_of_pfree h_g)
    · exact OutcomeStable.misereGE_zero_of_misereOutcome_R h_g h_out

/--
Unwinding `1 ≱ g` when $\operatorname{o}(G) = \mathscr{R}$: some Left option `gl` of `g` is not
`≤ 0` and has no Right option `≤ 1`.
-/
theorem not_one_misereGE_cases
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g : GameForm} (h_g : PFreeSubset U g)
    (h_out : MisereOutcome g = .R) (h_not_ge : ¬ (1 : GameForm) ≥m (PFreeSubset U) g) :
    ∃ gl ∈ moves .left g, ¬ (0 : GameForm) ≥m (PFreeSubset U) gl ∧
      ∀ glr ∈ moves .right gl, ¬ (1 : GameForm) ≥m (PFreeSubset U) glr := by
  by_contra h_contra
  push_neg at h_contra
  apply h_not_ge
  refine PFreeBlocking.misereGE_of_maintenance_proviso isPFree_one h_g.isPFree ?_ ?_ ?_ ?_
  · intro gr h_gr
    rw [rightMoves_one] at h_gr
    exact absurd h_gr (Set.notMem_empty _)
  · intro hl h_hl
    by_cases h_ge : (0 : GameForm) ≥m (PFreeSubset U) hl
    · left
      refine ⟨0, ?_, h_ge⟩
      rw [leftMoves_one]
      exact Set.mem_singleton _
    · obtain ⟨hlr, h_hlr, h_hlr_ge⟩ := h_contra hl h_hl h_ge
      exact Or.inr ⟨hlr, h_hlr, h_hlr_ge⟩
  · intro _
    rw [h_out]
    decide
  · intro h_end
    exact absurd (winsGoingFirst_of_isEnd h_end)
      (misereOutcome_R_iff_winsGoingFirst.mp h_out).right

/--
For `n ≤ 0`: if `n + 1 ≱ g` then `g ≥ n`, or some Left option of `g` is `≥ n - 1`.
-/
theorem misereGE_intCast_or_exists_leftMove_of_not_succ_misereGE
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g : GameForm}
    (h_g : PFreeSubset U g) {n : ℤ} (h_n : n ≤ 0)
    (h_not_ge : ¬ ((n + 1 : ℤ) : GameForm) ≥m (PFreeSubset U) g) :
    g ≥m (PFreeSubset U) ((n : ℤ) : GameForm) ∨
      ∃ gl ∈ moves .left g, gl ≥m (PFreeSubset U) ((n - 1 : ℤ) : GameForm) := by
  rcases h_n.lt_or_eq with h_neg | h_zero
  · have h_n1 : n + 1 ≤ 0 := by omega
    rcases not_intCast_misereGE_cases h_n1 h_g h_not_ge with h_B | ⟨gl, h_gl, h_gl_not, h_A⟩
    · have h_not_isEnd : ¬ IsEnd .right g := fun h_end =>
        h_not_ge (Blocking.intCast_misereGE_of_isEnd_right h_g h_n1 h_end)
      have h_out : MisereOutcome g ≠ .R := fun h_out =>
        h_not_ge (OutcomeStable.intCast_misereGE_of_misereOutcome_R h_g h_n1 h_out)
      left
      refine misereGE_intCast_of_forall_rightMoves (by omega) h_g h_not_isEnd h_out ?_
      intro gr h_gr
      have h_gr_mem := Hereditary.of_mem_moves h_g h_gr
      rcases misereGE_intCast_or_exists_leftMove_of_not_succ_misereGE h_gr_mem h_n1 (h_B gr h_gr)
        with h_ge | ⟨grl, h_grl, h_ge⟩
      · exact Or.inl h_ge
      · right
        refine ⟨grl, h_grl, ?_⟩
        rwa [add_sub_cancel_right] at h_ge
    · right
      refine ⟨gl, h_gl, ?_⟩
      have h_gl_mem := Hereditary.of_mem_moves h_g h_gl
      have h_not_isEnd : ¬ IsEnd .right gl := fun h_end =>
        h_gl_not (Blocking.intCast_misereGE_of_isEnd_right h_gl_mem (by omega) h_end)
      have h_out : MisereOutcome gl ≠ .R := fun h_out =>
        h_gl_not (OutcomeStable.intCast_misereGE_of_misereOutcome_R h_gl_mem (by omega) h_out)
      refine misereGE_intCast_of_forall_rightMoves (by omega) h_gl_mem h_not_isEnd h_out ?_
      intro glr h_glr
      have h_glr_mem := Hereditary.of_mem_moves h_gl_mem h_glr
      rw [sub_add_cancel]
      exact misereGE_intCast_or_exists_leftMove_of_not_succ_misereGE h_glr_mem h_n (h_A glr h_glr)
  · subst h_zero
    rw [zero_add, Form.intCast_one] at h_not_ge
    by_cases h_isEnd : IsEnd .left g
    · left
      have := Blocking.isEnd_left_misereGE_zero h_g h_isEnd
      rwa [← Form.intCast_zero] at this
    cases h_out : MisereOutcome g
    · left
      exact OutcomeStable.misereGE_zero_of_misereOutcome_L h_g h_out
    · right
      have h_win := (misereOutcome_N_iff_winsGoingFirst.mp h_out).left
      rw [winsGoingFirst_iff] at h_win
      rcases h_win with h_end | ⟨gl, h_gl, h_gl_not_win⟩
      · exact absurd (isEndLike_iff_isEnd.mp h_end) h_isEnd
      have h_gl_mem := Hereditary.of_mem_moves h_g h_gl
      rw [Player.neg_left] at h_gl_not_win
      refine ⟨gl, h_gl, ?_⟩
      rw [Int.zero_sub]
      exact misereGE_neg_one_of_misereOutcome_L h_gl_mem
        (misereOutcome_of_not_winsGoingFirst h_gl_mem.isPFree h_gl_not_win)
    · exact absurd h_out (misereOutcome_ne_P_of_pfree h_g)
    · right
      obtain ⟨gl, h_gl, h_gl_not, h_A⟩ := not_one_misereGE_cases h_g h_out h_not_ge
      refine ⟨gl, h_gl, ?_⟩
      have h_gl_mem := Hereditary.of_mem_moves h_g h_gl
      have h_not_isEnd : ¬ IsEnd .right gl := fun h_end =>
        h_gl_not (Blocking.isEnd_right_zero_misereGE h_gl_mem h_end)
      have h_gl_out : MisereOutcome gl ≠ .R := fun h_out' =>
        h_gl_not (OutcomeStable.misereGE_zero_of_misereOutcome_R h_gl_mem h_out')
      rw [Int.zero_sub]
      refine misereGE_intCast_of_forall_rightMoves le_rfl h_gl_mem h_not_isEnd h_gl_out ?_
      intro glr h_glr
      have h_glr_mem := Hereditary.of_mem_moves h_gl_mem h_glr
      have h_glr_not_ge : ¬ ((0 + 1 : ℤ) : GameForm) ≥m (PFreeSubset U) glr := by
        rw [zero_add, Form.intCast_one]
        exact h_A glr h_glr
      have ih := misereGE_intCast_or_exists_leftMove_of_not_succ_misereGE h_glr_mem le_rfl
        h_glr_not_ge
      rw [Int.zero_sub] at ih
      rwa [show (-1 + 1 : ℤ) = 0 by omega]
termination_by g
decreasing_by form_wf

open Classical in
/--
If $G \in \operatorname{pf}(\mathcal{U})$ is a Left end,
then it is equivalent to some non-positive integer.
-/
theorem isEnd_left_exists_intCast_misereEQ'
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    [ClosedUnderAdd U] {g : GameForm}
    (h_g : PFreeSubset U g) (h_isEnd : IsEnd .left g) :
    ∃ n : ℕ, g =m (PFreeSubset U) ((-(n : ℤ) : ℤ) : GameForm) := by
  have h_ex := IntegerInvertible.exists_neg_natCast_misereGE h_g (Short.isShort h_g)
  refine ⟨Nat.find h_ex, ?_⟩
  have h_ge : ((-(Nat.find h_ex : ℤ) : ℤ) : GameForm) ≥m (PFreeSubset U) g := Nat.find_spec h_ex
  have h_not_ge : ¬ ((-(Nat.find h_ex : ℤ) + 1 : ℤ) : GameForm) ≥m (PFreeSubset U) g := by
    intro h_succ
    rcases Nat.eq_zero_or_pos (Nat.find h_ex) with h_zero | h_pos
    · rw [h_zero] at h_succ
      simp only [Nat.cast_zero, neg_zero, zero_add, Form.intCast_one] at h_succ
      exact (misereOutcome_R_iff_winsGoingFirst.mp (misereOutcome_R_of_one_misereGE h_succ)).right
        (winsGoingFirst_of_isEnd h_isEnd)
    · refine Nat.find_min h_ex (show Nat.find h_ex - 1 < Nat.find h_ex by omega) ?_
      have h_cast : (-((Nat.find h_ex - 1 : ℕ) : ℤ) : ℤ) = -(Nat.find h_ex : ℤ) + 1 := by omega
      rw [h_cast]
      exact h_succ
  rcases misereGE_intCast_or_exists_leftMove_of_not_succ_misereGE h_g (by omega) h_not_ge
    with h_le | ⟨gl, h_gl, -⟩
  · exact MisereEq.of_antisymm h_le h_ge
  · exact absurd h_gl (not_mem_moves_of_isEnd h_isEnd)

/--
If $G \in \operatorname{pf}(\mathcal{U})$ is a Right end,
then it is equivalent to some non-negative integer.
-/
theorem isEnd_right_exists_intCast_misereEQ'
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    [ClosedUnderAdd U] {g : GameForm}
    (h_g : PFreeSubset U g) (h_isEnd : IsEnd .right g) :
    ∃ n : ℕ, g =m (PFreeSubset U) ((n : ℤ) : GameForm) := by
  obtain ⟨n, h_n⟩ := isEnd_left_exists_intCast_misereEQ' (ClosedUnderNeg.neg_of h_g)
    (IsEnd.neg_iff_neg.mpr h_isEnd)
  refine ⟨n, ?_⟩
  rwa [Form.intCast_neg, misereEQ_neg_iff] at h_n

/--
If $G \in \operatorname{pf}(\mathcal{U})$ is an end,
then it is equivalent to some integer.
-/
theorem isEnd_exists_intCast_misereEQ'
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    [ClosedUnderAdd U] {p : Player} {g : GameForm}
    (h_g : PFreeSubset U g) (h_isEnd : IsEnd p g) :
    ∃ k : ℤ, g =m (PFreeSubset U) ((k : ℤ) : GameForm) := by
  cases p
  · obtain ⟨n, h_n⟩ := isEnd_left_exists_intCast_misereEQ' h_g h_isEnd
    exact ⟨-(n : ℤ), h_n⟩
  · obtain ⟨n, h_n⟩ := isEnd_right_exists_intCast_misereEQ' h_g h_isEnd
    exact ⟨(n : ℤ), h_n⟩

/--
Every end of $\operatorname{pf}(\mathcal{B})$ is equivalent to an integer.
-/
theorem PFreeBlocking.isEnd_exists_intCast_misereEQ {p : Player} {g : GameForm}
    (h_g : PFreeBlocking g) (h_isEnd : IsEnd p g) :
    ∃ k : ℤ, g =m PFreeBlocking ((k : ℤ) : GameForm) :=
  isEnd_exists_intCast_misereEQ' h_g h_isEnd

end PFree
