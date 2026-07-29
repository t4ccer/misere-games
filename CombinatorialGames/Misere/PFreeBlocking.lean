/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.Blocking

public section

universe u

open Form
open Form.Misere.Outcome
open GameForm
open PFree

namespace GameForm

abbrev PFreeBlocking : GameForm → Prop := PFreeSubset ShortBlocking

/-- If `A` is a blocking universe then so is `pf(A) = PFreeSubset A`. -/
instance instBlockingPFreeSubset {A : GameForm → Prop} [Blocking A] :
    Blocking (PFreeSubset A) where
  isBlocking h := Form.Blocking.isBlocking h.mem

private theorem misereOutcome_L_of_not_winsGoingFirst_right {g : GameForm}
    (hpf : IsPFree g) (h : ¬ WinsGoingFirst .right g) : MisereOutcome g = .L := by
  rw [misereOutcome_L_iff_winsGoingFirst]
  refine ⟨?_, h⟩
  by_contra hc
  exact misereOutcome_ne_P_of_pfree hpf (misereOutcome_P_iff_winsGoingFirst.mpr ⟨h, hc⟩)

/--
If `G, H ∈ pf(B)` with `o(G) = L` and `H` a Left end, then `o(G + H) = L`.

This is [Davies, Miller, Milley (Lemma 4.1 on p.
24)][davies:SumsPFreeForms:2025]
-/
theorem misereOutcome_L_add_isEnd_left {A : GameForm → Prop} [Blocking A] [Hereditary A]
    {g h : GameForm}
    (hg : (PFreeSubset A) g) (hh : (PFreeSubset A) h)
    (hgL : MisereOutcome g = .L) (hhe : IsEnd .left h) : MisereOutcome (g + h) = .L := by
  have hg_out := misereOutcome_L_iff_winsGoingFirst.mp hgL
  rw [misereOutcome_L_iff_winsGoingFirst]
  constructor
  · rcases (winsGoingFirst_iff g .left).mp hg_out.left with hg_end | ⟨gl, hgl, hgl_not_right⟩
    · exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨isEndLike_iff_isEnd.mp hg_end, hhe⟩)
    · have hgl_pfb := Hereditary.of_mem_moves hg hgl
      have hglL := misereOutcome_L_of_not_winsGoingFirst_right hgl_pfb.isPFree hgl_not_right
      have hsum := misereOutcome_L_add_isEnd_left hgl_pfb hh hglL hhe
      exact winsGoingFirst_of_moves
        ⟨gl + h, add_right_mem_moves_add hgl h, (misereOutcome_L_iff_winsGoingFirst.mp hsum).right⟩
  · rw [not_winsGoingFirst_iff]
    refine ⟨fun h_end => ?_, fun gr hgr => ?_⟩
    · absurd hg_out.right
      exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mp (isEndLike_iff_isEnd.mp h_end)).left
    · rw [moves_add, Set.mem_union, Set.mem_image] at hgr
      rw [Player.neg_right]
      rcases hgr with ⟨gr', hgr', rfl⟩ | ⟨hr, hhr, rfl⟩
      · have h_left_gr' : WinsGoingFirst .left gr' := by
          simpa [Player.neg_right] using (not_winsGoingFirst_iff.mp hg_out.right).right gr' hgr'
        have hgr_pfb := Hereditary.of_mem_moves hg hgr'
        rcases (winsGoingFirst_iff gr' .left).mp h_left_gr'
            with hgr_end | ⟨grl, hgrl, hgrl_not_right⟩
        · exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨isEndLike_iff_isEnd.mp hgr_end, hhe⟩)
        · apply winsGoingFirst_of_moves
          use grl + h
          constructor
          · exact add_right_mem_moves_add hgrl h
          · have hgrl_pfb := Hereditary.of_mem_moves hgr_pfb hgrl
            have hgrlL := misereOutcome_L_of_not_winsGoingFirst_right hgrl_pfb.isPFree hgrl_not_right
            have hsum := misereOutcome_L_add_isEnd_left hgrl_pfb hh hgrlL hhe
            exact (misereOutcome_L_iff_winsGoingFirst.mp hsum).right
      · have hh_be : IsBlockedEnd .left h := isBlockedEnd_of_isBlocking (Blocking.isBlocking hh.mem) hhe
        rcases IsBlockedEnd.hereditary_def hh_be hr hhr with hr_be | ⟨hrl, hhrl, hrl_be⟩
        · have hr_pfb := Hereditary.of_mem_moves hh hhr
          have hsum := misereOutcome_L_add_isEnd_left hg hr_pfb hgL (isEnd_of_isBlockedEnd hr_be)
          exact (misereOutcome_L_iff_winsGoingFirst.mp hsum).left
        · apply winsGoingFirst_of_moves
          use g + hrl
          constructor
          · exact add_left_mem_moves_add hhrl g
          · have hrl_pfb := Hereditary.of_mem_moves (Hereditary.of_mem_moves hh hhr) hhrl
            have hsum := misereOutcome_L_add_isEnd_left hg hrl_pfb hgL (isEnd_of_isBlockedEnd hrl_be)
            exact (misereOutcome_L_iff_winsGoingFirst.mp hsum).right
termination_by Form.birthday g + Form.birthday h
decreasing_by
  all_goals
    first
      | exact birthday_add_lt_left (birthday_lt_of_mem_moves (by assumption))
      | exact birthday_add_lt_right (birthday_lt_of_mem_moves (by assumption))
      | exact birthday_add_lt_left
          (lt_trans (birthday_lt_of_mem_moves (by assumption)) (birthday_lt_of_mem_moves (by assumption)))
      | exact birthday_add_lt_right
          (lt_trans (birthday_lt_of_mem_moves (by assumption)) (birthday_lt_of_mem_moves (by assumption)))

/--
This is the mirror of [Davies, Miller, Milley (Lemma 4.1 on p.
24)][davies:SumsPFreeForms:2025].
-/
theorem misereOutcome_R_add_isEnd_right {A : GameForm → Prop}
    [Blocking A] [Hereditary A] [ClosedUnderNeg A]
    {g h : GameForm}
    (hg : (PFreeSubset A) g) (hh : (PFreeSubset A) h)
    (hgR : MisereOutcome g = .R) (hhe : IsEnd .right h) : MisereOutcome (g + h) = .R := by
  rw [← misereOutcome_neg_L_iff_misereOutcome]
  simpa [neg_add_rev, add_comm]
    using misereOutcome_L_add_isEnd_left
            (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
            (misereOutcome_neg_L_iff_misereOutcome.mpr hgR) (IsEnd.neg_iff_neg.mpr hhe)

mutual

private theorem misereOutcome_of_add_LL_blocking
    {A : GameForm → Prop} [Blocking A] [Hereditary A] [ClosedUnderNeg A]
    {g h : GameForm} (hg : (PFreeSubset A) g) (hh : (PFreeSubset A) h)
    (hgL : MisereOutcome g = .L) (hhL : MisereOutcome h = .L) : MisereOutcome (g + h) = .L := by
  have hg_out := misereOutcome_L_iff_winsGoingFirst.mp hgL
  have hh_out := misereOutcome_L_iff_winsGoingFirst.mp hhL
  rw [misereOutcome_L_iff_winsGoingFirst]
  constructor
  · rcases (winsGoingFirst_iff g .left).mp hg_out.left with hg_end | ⟨gl, hgl, hgl_not_right⟩
    · rcases (winsGoingFirst_iff h .left).mp hh_out.left with hh_end | ⟨hl, hhl, hhl_not_right⟩
      · exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr
          ⟨isEndLike_iff_isEnd.mp hg_end, isEndLike_iff_isEnd.mp hh_end⟩)
      · have hhl_pfb := Hereditary.of_mem_moves hh hhl
        have hhlL := misereOutcome_L_of_not_winsGoingFirst_right hhl_pfb.isPFree hhl_not_right
        have hsumL := misereOutcome_of_add_LL_blocking hg hhl_pfb hgL hhlL
        exact winsGoingFirst_of_moves
          ⟨g + hl, add_left_mem_moves_add hhl g, (misereOutcome_L_iff_winsGoingFirst.mp hsumL).right⟩
    · have hgl_pfb := Hereditary.of_mem_moves hg hgl
      have hglL := misereOutcome_L_of_not_winsGoingFirst_right hgl_pfb.isPFree hgl_not_right
      have hsumL := misereOutcome_of_add_LL_blocking hgl_pfb hh hglL hhL
      exact winsGoingFirst_of_moves
        ⟨gl + h, add_right_mem_moves_add hgl h, (misereOutcome_L_iff_winsGoingFirst.mp hsumL).right⟩
  · rw [not_winsGoingFirst_iff]
    refine ⟨fun h_end => ?_, fun gr hgr => ?_⟩
    · exact hg_out.right (winsGoingFirst_of_isEnd (IsEnd.add_iff.mp (isEndLike_iff_isEnd.mp h_end)).left)
    · rw [moves_add, Set.mem_union, Set.mem_image] at hgr
      rcases hgr with ⟨gr', hgr', rfl⟩ | ⟨hr, hhr, rfl⟩
      · have h_left_gr' : WinsGoingFirst .left gr' := by
          simpa [Player.neg_right] using (not_winsGoingFirst_iff.mp hg_out.right).right gr' hgr'
        have hgr_pfb := Hereditary.of_mem_moves hg hgr'
        cases hgr'_out : MisereOutcome gr' with
        | L => exact (misereOutcome_L_iff_winsGoingFirst.mp
            (misereOutcome_of_add_LL_blocking hgr_pfb hh hgr'_out hhL)).left
        | N =>
            have hwin : WinsGoingFirst .left (h + gr') :=
              miserePlayerOutcome_eq_iff_winsGoingFirst.mp
                (miserePlayerOutcome_of_add_LN_blocking hh hgr_pfb hhL hgr'_out)
            rwa [add_comm] at hwin
        | P => exact absurd hgr'_out (misereOutcome_ne_P_of_pfree hgr_pfb.isPFree)
        | R => exact absurd h_left_gr' (misereOutcome_R_iff_winsGoingFirst.mp hgr'_out).right
      · have h_left_hr : WinsGoingFirst .left hr := by
          simpa [Player.neg_right] using (not_winsGoingFirst_iff.mp hh_out.right).right hr hhr
        have hhr_pfb := Hereditary.of_mem_moves hh hhr
        cases hhr_out : MisereOutcome hr with
        | L => exact (misereOutcome_L_iff_winsGoingFirst.mp
            (misereOutcome_of_add_LL_blocking hg hhr_pfb hgL hhr_out)).left
        | N =>
            exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp
              (miserePlayerOutcome_of_add_LN_blocking hg hhr_pfb hgL hhr_out)
        | P => exact absurd hhr_out (misereOutcome_ne_P_of_pfree hhr_pfb.isPFree)
        | R => exact absurd h_left_hr (misereOutcome_R_iff_winsGoingFirst.mp hhr_out).right
termination_by Form.birthday g + Form.birthday h
decreasing_by all_goals gameform_birthday

private theorem miserePlayerOutcome_of_add_LN_blocking
    {A : GameForm → Prop} [Blocking A] [Hereditary A] [ClosedUnderNeg A]
    {g h : GameForm} (hg : (PFreeSubset A) g) (hh : (PFreeSubset A) h)
    (hgL : MisereOutcome g = .L) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .left = .left := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst]
  by_cases h_end : IsEnd .left h
  · exact (misereOutcome_L_iff_winsGoingFirst.mp (misereOutcome_L_add_isEnd_left hg hh hgL h_end)).left
  · rcases (winsGoingFirst_iff h .left).mp (misereOutcome_N_iff_winsGoingFirst.mp hhN).left with
        h_le | ⟨hl, hhl, hhl_not_right⟩
    · exact absurd (isEndLike_iff_isEnd.mp h_le) h_end
    · have hhl_pfb := Hereditary.of_mem_moves hh hhl
      have hhlL := misereOutcome_L_of_not_winsGoingFirst_right hhl_pfb.isPFree hhl_not_right
      refine winsGoingFirst_of_moves ⟨g + hl, add_left_mem_moves_add hhl g, ?_⟩
      rw [Player.neg_left]
      exact (misereOutcome_L_iff_winsGoingFirst.mp
        (misereOutcome_of_add_LL_blocking hg hhl_pfb hgL hhlL)).right
termination_by Form.birthday g + Form.birthday h
decreasing_by all_goals gameform_birthday

end

private theorem misereOutcome_of_add_RR_blocking
    {A : GameForm → Prop} [Blocking A] [Hereditary A] [ClosedUnderNeg A]
    {g h : GameForm} (hg : (PFreeSubset A) g) (hh : (PFreeSubset A) h)
    (hgR : MisereOutcome g = .R) (hhR : MisereOutcome h = .R) : MisereOutcome (g + h) = .R := by
  rw [← misereOutcome_neg_L_iff_misereOutcome]
  simpa [neg_add_rev, add_comm]
    using misereOutcome_of_add_LL_blocking
            (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
            (misereOutcome_neg_L_iff_misereOutcome.mpr hgR)
            (misereOutcome_neg_L_iff_misereOutcome.mpr hhR)

private theorem miserePlayerOutcome_of_add_RN_blocking
    {A : GameForm → Prop} [Blocking A] [Hereditary A] [ClosedUnderNeg A]
    {g h : GameForm} (hg : (PFreeSubset A) g) (hh : (PFreeSubset A) h)
    (hgR : MisereOutcome g = .R) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .right = .right := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst, ← Player.neg_left, ← winsGoingFirst_neg_iff]
  simpa [neg_add_rev, add_comm]
    using miserePlayerOutcome_eq_iff_winsGoingFirst.mp
          (miserePlayerOutcome_of_add_LN_blocking
            (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
            (misereOutcome_neg_L_iff_misereOutcome.mpr hgR)
            (misereOutcome_neg_N_iff_misereOutcome.mpr hhN))

/--
This is [Davies, Miller, Milley (Lemma 4.2 on p.
25)][davies:SumsPFreeForms:2025].
-/
instance : OutcomeStable (ShortBlocking (G := GameForm)) where
  misereOutcome_of_add_LL := misereOutcome_of_add_LL_blocking
  misereOutcome_of_add_RR := misereOutcome_of_add_RR_blocking
  miserePlayerOutcome_of_add_LN := miserePlayerOutcome_of_add_LN_blocking
  miserePlayerOutcome_of_add_RN := miserePlayerOutcome_of_add_RN_blocking

private theorem misereOutcome_R_of_not_winsGoingFirst_left {g : GameForm}
    (hpf : IsPFree g) (h : ¬ WinsGoingFirst .left g) : MisereOutcome g = .R := by
  rw [misereOutcome_R_iff_winsGoingFirst]
  refine ⟨?_, h⟩
  by_contra hc
  exact misereOutcome_ne_P_of_pfree hpf (misereOutcome_P_iff_winsGoingFirst.mpr ⟨hc, h⟩)

/--
This is [Davies, Miller, Milley (Lemma 4.7 on p.
26)][davies:SumsPFreeForms:2025].
-/
theorem miserePlayerOutcome_right_isEnd_left_NN
    {A : GameForm → Prop} [Blocking A] [Hereditary A] [OutcomeStable A] [ClosedUnderNeg A]
    {g h : GameForm} (hg : (PFreeSubset A) g) (hh : (PFreeSubset A) h)
    (hge : IsEnd .left g) (hgN : MisereOutcome g = .N) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .right = .right := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst]
  by_cases hgr_end : IsEnd .right g
  · have hg0 : g = 0 := both_ends_eq_zero hge hgr_end
    subst hg0
    rw [zero_add]
    exact (misereOutcome_N_iff_winsGoingFirst.mp hhN).right
  · obtain ⟨gr, hgr_mem, hgr_not⟩ : ∃ gr ∈ moves .right g, ¬ WinsGoingFirst .left gr := by
      rcases (winsGoingFirst_iff g .right).mp (misereOutcome_N_iff_winsGoingFirst.mp hgN).right
          with hend | ⟨gr, hgr, hgr_not⟩
      · exact absurd (isEndLike_iff_isEnd.mp hend) hgr_end
      · exact ⟨gr, hgr, by simpa [Player.neg_right] using hgr_not⟩
    have hgrR := misereOutcome_R_of_not_winsGoingFirst_left
        (Hereditary.of_mem_moves hg hgr_mem).isPFree hgr_not
    by_cases hhr_end : IsEnd .right h
    · refine winsGoingFirst_of_moves ⟨gr + h, add_right_mem_moves_add hgr_mem h, ?_⟩
      rw [Player.neg_right]
      exact (misereOutcome_R_iff_winsGoingFirst.mp
        (misereOutcome_R_add_isEnd_right (Hereditary.of_mem_moves hg hgr_mem) hh hgrR hhr_end)).right
    · obtain ⟨hr, hhr_mem, hhr_not⟩ : ∃ hr ∈ moves .right h, ¬ WinsGoingFirst .left hr := by
        rcases (winsGoingFirst_iff h .right).mp (misereOutcome_N_iff_winsGoingFirst.mp hhN).right
            with hend | ⟨hr, hhr, hhr_not⟩
        · exact absurd (isEndLike_iff_isEnd.mp hend) hhr_end
        · exact ⟨hr, hhr, by simpa [Player.neg_right] using hhr_not⟩
      have hhr_pfb := Hereditary.of_mem_moves hh hhr_mem
      have hhrR : MisereOutcome hr = .R :=
        misereOutcome_R_of_not_winsGoingFirst_left hhr_pfb.isPFree hhr_not
      have hhr_not_lend : ¬ IsEnd .left hr := by
        intro he
        exact hhr_not (winsGoingFirst_of_isEnd he)
      refine winsGoingFirst_of_moves ⟨g + hr, add_left_mem_moves_add hhr_mem g, ?_⟩
      rw [Player.neg_right, not_winsGoingFirst_iff]
      refine ⟨?_, fun g' hg' => ?_⟩
      · rw [GameForm.isEndLike_iff_isEnd, IsEnd.add_iff]
        exact fun hc => hhr_not_lend hc.right
      · rw [Player.neg_left]
        rw [moves_add, Set.mem_union, Set.mem_image, Set.mem_image] at hg'
        rcases hg' with ⟨gl, hgl, rfl⟩ | ⟨hrl, hhrl, rfl⟩
        · have hg0 : moves .left g = ∅ := by rw [← isEnd_def]; exact hge
          rw [hg0] at hgl
          exact (Set.notMem_empty gl hgl).elim
        · have hhrl_pfb := Hereditary.of_mem_moves hhr_pfb hhrl
          have hhrl_winsR : WinsGoingFirst .right hrl := by
            have := (not_winsGoingFirst_iff.mp
                      (misereOutcome_R_iff_winsGoingFirst.mp hhrR).right).right hrl hhrl
            rwa [Player.neg_left] at this
          rcases hhrl_out : MisereOutcome hrl with _ | _ | _ | _
          · absurd (misereOutcome_L_iff_winsGoingFirst.mp hhrl_out).right
            exact hhrl_winsR
          · exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp
              (miserePlayerOutcome_right_isEnd_left_NN hg hhrl_pfb hge hgN hhrl_out)
          · exact absurd hhrl_out (misereOutcome_ne_P_of_pfree hhrl_pfb.isPFree)
          · have hwin : MiserePlayerOutcome (hrl + g) .right = .right :=
              OutcomeStable.miserePlayerOutcome_of_add_RN hhrl_pfb hg hhrl_out hgN
            have := miserePlayerOutcome_eq_iff_winsGoingFirst.mp hwin
            rwa [add_comm] at this
termination_by Form.birthday g + Form.birthday h
decreasing_by
  all_goals
    first
      | exact birthday_add_lt_left (birthday_lt_of_mem_moves (by assumption))
      | exact birthday_add_lt_right (birthday_lt_of_mem_moves (by assumption))
      | exact birthday_add_lt_right
          (lt_trans (birthday_lt_of_mem_moves (by assumption)) (birthday_lt_of_mem_moves (by assumption)))

/--
This is the mirror of [Davies, Miller, Milley (Lemma 4.7 on p.
26)][davies:SumsPFreeForms:2025].
-/
theorem miserePlayerOutcome_left_isEnd_right_NN
    {A : GameForm → Prop} [Blocking A] [Hereditary A] [OutcomeStable A] [ClosedUnderNeg A]
    {g h : GameForm} (hg : (PFreeSubset A) g) (hh : (PFreeSubset A) h)
    (hge : IsEnd .right g) (hgN : MisereOutcome g = .N) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .left = .left := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst, ← Player.neg_right, ← winsGoingFirst_neg_iff]
  simpa [neg_add_rev, add_comm]
    using miserePlayerOutcome_eq_iff_winsGoingFirst.mp
      (miserePlayerOutcome_right_isEnd_left_NN
        (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
        (IsEnd.neg_iff_neg.mpr hge) (misereOutcome_neg_N_iff_misereOutcome.mpr hgN)
        (misereOutcome_neg_N_iff_misereOutcome.mpr hhN))

theorem miserePlayerOutcome_right_isEnd_right_NN
    {A : GameForm → Prop} [Blocking A] [Hereditary A] [OutcomeStable A] [ClosedUnderNeg A]
    {g h : GameForm} (hg : (PFreeSubset A) g) (hh : (PFreeSubset A) h)
    (hge : IsEnd .right g) (hgN : MisereOutcome g = .N) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .right = .right := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst]
  by_cases hhr_end : IsEnd .right h
  · exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨hge, hhr_end⟩)
  · obtain ⟨hr, hhr_mem, hhr_not⟩ : ∃ hr ∈ moves .right h, ¬ WinsGoingFirst .left hr := by
      rcases (winsGoingFirst_iff h .right).mp (misereOutcome_N_iff_winsGoingFirst.mp hhN).right
          with hend | ⟨hr, hhr, hhr_not⟩
      · exact absurd (isEndLike_iff_isEnd.mp hend) hhr_end
      · exact ⟨hr, hhr, by simpa [Player.neg_right] using hhr_not⟩
    have hhr_pfb := Hereditary.of_mem_moves hh hhr_mem
    have hhrR := misereOutcome_R_of_not_winsGoingFirst_left hhr_pfb.isPFree hhr_not
    have hhr_not_lend : ¬ IsEnd .left hr := fun he => hhr_not (winsGoingFirst_of_isEnd he)
    refine winsGoingFirst_of_moves ⟨g + hr, add_left_mem_moves_add hhr_mem g, ?_⟩
    rw [Player.neg_right, not_winsGoingFirst_iff]
    refine ⟨?_, fun y hy => ?_⟩
    · rw [GameForm.isEndLike_iff_isEnd, IsEnd.add_iff]
      exact fun hc => hhr_not_lend hc.right
    · rw [Player.neg_left]
      rw [moves_add, Set.mem_union, Set.mem_image, Set.mem_image] at hy
      rcases hy with ⟨gl, hgl, rfl⟩ | ⟨hrl, hhrl, rfl⟩
      · have hgl_pfb := Hereditary.of_mem_moves hg hgl
        have hg_blocked : IsBlockedEnd .right g :=
          isBlockedEnd_of_isBlocking (Blocking.isBlocking hg) hge
        rcases IsBlockedEnd.hereditary_def hg_blocked gl hgl with hgl_be | ⟨glr, hglr_mem, hglr_be⟩
        · have hsum := misereOutcome_R_add_isEnd_right hhr_pfb hgl_pfb hhrR (isEnd_of_isBlockedEnd hgl_be)
          rw [add_comm] at hsum
          exact (misereOutcome_R_iff_winsGoingFirst.mp hsum).left
        · have hglr_pfb := Hereditary.of_mem_moves hgl_pfb hglr_mem
          apply winsGoingFirst_of_moves
          refine ⟨glr + hr, add_right_mem_moves_add hglr_mem hr, ?_⟩
          have hsum := misereOutcome_R_add_isEnd_right hhr_pfb hglr_pfb hhrR (isEnd_of_isBlockedEnd hglr_be)
          rw [add_comm] at hsum
          rw [Player.neg_right]
          exact (misereOutcome_R_iff_winsGoingFirst.mp hsum).right
      · have hhrl_pfb := Hereditary.of_mem_moves hhr_pfb hhrl
        have hhrl_winsR : WinsGoingFirst .right hrl := by
          have := (not_winsGoingFirst_iff.mp (misereOutcome_R_iff_winsGoingFirst.mp hhrR).right).right hrl hhrl
          rwa [Player.neg_left] at this
        rcases hhrl_out : MisereOutcome hrl with _ | _ | _ | _
        · exact absurd hhrl_winsR (misereOutcome_L_iff_winsGoingFirst.mp hhrl_out).right
        · exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp
            (miserePlayerOutcome_right_isEnd_right_NN hg hhrl_pfb hge hgN hhrl_out)
        · exact absurd hhrl_out (misereOutcome_ne_P_of_pfree hhrl_pfb.isPFree)
        · have hwin : MiserePlayerOutcome (hrl + g) .right = .right :=
            OutcomeStable.miserePlayerOutcome_of_add_RN hhrl_pfb hg hhrl_out hgN
          have := miserePlayerOutcome_eq_iff_winsGoingFirst.mp hwin
          rwa [add_comm] at this
termination_by h
decreasing_by form_wf

private theorem misereOutcome_N_isEnd_right_NN
    {A : GameForm → Prop} [Blocking A] [Hereditary A] [OutcomeStable A] [ClosedUnderNeg A]
    {g h : GameForm} (hg : (PFreeSubset A) g) (hh : (PFreeSubset A) h)
    (hge : IsEnd .right g) (hgN : MisereOutcome g = .N) (hhN : MisereOutcome h = .N) :
    MisereOutcome (g + h) = .N := by
  rw [misereOutcome_N_iff_miserePlayerOutcome]
  exact ⟨ miserePlayerOutcome_left_isEnd_right_NN hg hh hge hgN hhN
        , miserePlayerOutcome_right_isEnd_right_NN hg hh hge hgN hhN⟩

theorem misereOutcome_N_isEnd_NN
    {A : GameForm → Prop} [Blocking A] [Hereditary A] [OutcomeStable A] [ClosedUnderNeg A]
    {g h : GameForm} (hg : (PFreeSubset A) g) (hh : (PFreeSubset A) h)
    {p : Player} (hge : IsEnd p g) (hgN : MisereOutcome g = .N) (hhN : MisereOutcome h = .N) :
    MisereOutcome (g + h) = .N := by
  cases p
  · rw [<-neg_neg g, IsEnd.neg_iff_neg, Player.neg_left] at hge
    have := misereOutcome_N_isEnd_right_NN
              (ClosedUnderNeg.neg_of hg) (ClosedUnderNeg.neg_of hh) hge
              (misereOutcome_neg_N_iff_misereOutcome.mpr hgN)
              (misereOutcome_neg_N_iff_misereOutcome.mpr hhN)
    rwa [<-neg_add_rev, misereOutcome_neg_N_iff_misereOutcome, add_comm] at this
  · exact misereOutcome_N_isEnd_right_NN hg hh hge hgN hhN

/--
This is [Davies, Miller, Milley (Lemma 4.8 on p.
26)][davies:SumsPFreeForms:2025].
-/
instance : IntegerInvertible.PropertyX ShortBlocking where
  prop_left := by
    intro g h hAg hAh hsg hsh hNg hNh hge hnge hrg hlh
    rw [misereOutcome_N_iff_winsGoingFirst]
    refine ⟨?_, ?_⟩
    · obtain ⟨hl, hhl, hhl_not⟩ : ∃ hl ∈ moves .left h, ¬ WinsGoingFirst .right hl := by
        rcases (winsGoingFirst_iff h .left).mp (misereOutcome_N_iff_winsGoingFirst.mp hNh).left
            with hend | ⟨hl, hhl, hhl_not⟩
        · exact absurd (isEndLike_iff_isEnd.mp hend) hnge
        · exact ⟨hl, hhl, by simpa [Player.neg_left] using hhl_not⟩
      have hhl_pfb := Hereditary.of_mem_moves hAh hhl
      have hhlL := misereOutcome_L_of_not_winsGoingFirst_right hhl_pfb.isPFree hhl_not
      refine winsGoingFirst_of_moves ⟨g + hl, add_left_mem_moves_add hhl g, ?_⟩
      rw [Player.neg_left]
      have hsum : MisereOutcome (g + hl) = .L := by
        rw [add_comm]; exact misereOutcome_L_add_isEnd_left hhl_pfb hAg hhlL hge
      exact (misereOutcome_L_iff_winsGoingFirst.mp hsum).right
    · rw [<-miserePlayerOutcome_eq_iff_winsGoingFirst]
      exact miserePlayerOutcome_right_isEnd_left_NN hAg hAh hge hNg hNh
  prop_right := by
    intro g h hAg hAh hsg hsh hNg hNh hge hnge hlg hrh
    rw [misereOutcome_N_iff_winsGoingFirst]
    refine ⟨?_, ?_⟩
    · have hw := miserePlayerOutcome_eq_iff_winsGoingFirst.mp
        (miserePlayerOutcome_left_isEnd_right_NN hAh hAg hge hNh hNg)
      rwa [add_comm] at hw
    · obtain ⟨gr, hgr, hgr_not⟩ : ∃ gr ∈ moves .right g, ¬ WinsGoingFirst .left gr := by
        rcases (winsGoingFirst_iff g .right).mp (misereOutcome_N_iff_winsGoingFirst.mp hNg).right
            with hend | ⟨gr, hgr, hgr_not⟩
        · exact absurd (isEndLike_iff_isEnd.mp hend) hnge
        · exact ⟨gr, hgr, by simpa [Player.neg_right] using hgr_not⟩
      have hgr_pfb := Hereditary.of_mem_moves hAg hgr
      have hgrR := misereOutcome_R_of_not_winsGoingFirst_left hgr_pfb.isPFree hgr_not
      refine winsGoingFirst_of_moves ⟨gr + h, add_right_mem_moves_add hgr h, ?_⟩
      rw [Player.neg_right]
      exact (misereOutcome_R_iff_winsGoingFirst.mp
              (misereOutcome_R_add_isEnd_right hgr_pfb hAh hgrR hge)).right

/--
This is [Davies, Miller, Milley (Lemma 4.9 on p. 27)][davies:SumsPFreeForms:2025].
-/
instance : ClosedUnderAdd PFreeBlocking where
  has_add g h h_g h_h := by
    apply PFreeSubset.mk
    · exact ClosedUnderAdd.has_add g h h_g.mem h_h.mem
    · exact IntegerInvertible.isPFree_of_propertyX h_g h_h h_g.mem.short h_h.mem.short

theorem Strong.of_subset {p : Player} {A B : GameForm → Prop} {g : GameForm}
    (h_strong : Strong B g p) (h_subset : ∀ x, A x → B x) : Strong A g p := by
  unfold Strong at h_strong ⊢
  intro x h_x h_end
  exact h_strong x (h_subset x h_x) h_end

private theorem strong_of_not_misereOutcome {p : Player} {g : GameForm}
    (hg : PFreeBlocking g) (hout : MisereOutcome g ≠ Outcome.ofPlayer (-p)) :
    Strong PFreeBlocking g p := by
  apply Strong.of_subset
  · exact IsBlocking.strong_of_isStrongTest (PFree.isStrongTest hg.isPFree hout)
  · intro x h_x
    exact h_x.mem.blocking

private theorem strong_iff_misereOutcome_ne {p : Player} {g : GameForm}
    (hg : PFreeBlocking g) :
    Strong PFreeBlocking g p ↔ MisereOutcome g ≠ Outcome.ofPlayer (-p) := by
  constructor
  · intro hs hR
    have hw := hs 0 (HasZero.has_zero (A := PFreeBlocking))
      (isEndLike_of_isEnd isEnd_zero)
    rw [add_zero] at hw
    cases p
    · exact (misereOutcome_R_iff_winsGoingFirst.mp hR).right hw
    · exact (misereOutcome_L_iff_winsGoingFirst.mp hR).right hw
  · exact strong_of_not_misereOutcome hg

protected theorem PFreeBlocking.misereGE_of_maintenance_proviso
    {g h : GameForm} (hg : PFreeBlocking g) (hh : PFreeBlocking h)
    (h_m_r : Maintenance PFreeBlocking g h .right)
    (h_m_l : Maintenance PFreeBlocking g h .left)
    (h_p_r : IsEnd .right g → MisereOutcome h ≠ .L)
    (h_p_l : IsEnd .left h → MisereOutcome g ≠ .R) :
    g ≥m PFreeBlocking h := by
  apply Hereditary.misereGE_of_maintenance_proviso PFreeBlocking h_m_r h_m_l
  · intro h_end
    rw [isEndLike_iff_isEnd] at h_end
    rw [strong_iff_misereOutcome_ne]
    simp only [Player.neg_right, Outcome.ofPlayer_left, ne_eq, h_p_r h_end, not_false_eq_true]
    exact hh
  · intro h_end
    rw [isEndLike_iff_isEnd] at h_end
    rw [strong_iff_misereOutcome_ne]
    simp only [Player.neg_left, Outcome.ofPlayer_right, ne_eq, h_p_l h_end, not_false_eq_true]
    exact hg

protected theorem PFreeBlocking.add_neg_self_strong {p : Player} {g : GameForm} (hg : PFreeBlocking g) :
    Strong PFreeBlocking (g + -g) p := by
  rw [strong_iff_misereOutcome_ne (ClosedUnderAdd.has_add g (-g) hg (ClosedUnderNeg.neg_of hg))]
  intro h
  rw [misereOutcome_eq_player_iff, <-neg_neg (g + -g), winsGoingFirst_neg_iff] at h
  simp only [neg_add_rev, neg_neg, and_not_self] at h

/--
This is [Davies, Miller, Milley (Lemma 4.4 on p. 25)][davies:SumsPFreeForms:2025].
-/
theorem IsBlocking.strong_of_misereOutcome_ne_R {g : GameForm} (hg : IsPFree g)
    (h_out : MisereOutcome g ≠ .R) : Strong IsBlocking g .left := by
  apply IsBlocking.strong_of_isStrongTest
  apply PFree.isStrongTest hg
  simpa using h_out

/--
This is [Davies, Miller, Milley (Lemma 4.10 on p. 27)][davies:SumsPFreeForms:2025].
-/
protected theorem IsBlocking.add_neg_self_strong_left {g : GameForm}
    (hg : PFreeBlocking g) : Strong IsBlocking (g + -g) .left := by
  have h_add_mem := ClosedUnderAdd.has_add g (-g) hg (ClosedUnderNeg.neg_of hg)
  apply Or.elim (add_neg_self_misereOutcome g) <;> intro h_out
  · have := IsBlocking.strong_of_misereOutcome_ne_R h_add_mem.isPFree
    rw [h_out] at this
    exact this (by decide)
  · absurd h_out
    exact misereOutcome_ne_P_of_pfree (A := PFreeBlocking) h_add_mem

namespace Blocking

noncomputable abbrev Plugged (g : GameForm) : GameForm := !{(moves .left g) | {1}}

theorem plugged_misereOutcome
    {g : GameForm} :
    WinsGoingFirst .right (Plugged g) := by
  apply winsGoingFirst_of_moves
  simp only [rightMoves_ofSets, Set.mem_singleton_iff, Player.neg_right, exists_eq_left]
  exact (misereOutcome_R_iff_winsGoingFirst.mp one_misereOutcome_R).right

theorem plugged_mem
    {A : GameForm → Prop} [ShortUniverse A] [Blocking A] [OutcomeStable A] [HasInt A] [Short A]
    {g : GameForm} (h_g : (PFreeSubset A) g) (h_not_left : ¬ IsEnd .left g) :
    PFreeSubset A (Plugged g) := by
  apply PFree.pfreeSubset_short_ofSets
  · intro gl h_gl_mem
    exact Hereditary.of_mem_moves h_g h_gl_mem
  · simpa using HasNat.one
  · rw [isEnd_def] at h_not_left
    rwa [Set.nonempty_iff_ne_empty]
  · exact IsShort.finite_moves Player.left (Short.isShort h_g)
  · simp
  · simp
  · rw [misereOutcome_ne_P_iff_winsGoingFirst]
    apply Or.inl
    exact plugged_misereOutcome

theorem not_right_end_zero_ge
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g : GameForm} (h_g : (PFreeSubset U) g)
    (h_g_isEnd : IsEnd .right g) :
    0 ≥m (PFreeSubset U) g := by
  intro x h_x
  rw [zero_add]
  have h_g_out : MisereOutcome g = .N ∨ MisereOutcome g = .R := by
    cases h_g_out : MisereOutcome g
    · rw [misereOutcome_L_iff_winsGoingFirst] at h_g_out
      absurd h_g_out.right
      exact winsGoingFirst_of_isEnd h_g_isEnd
    · exact Or.inl rfl
    · absurd h_g_out
      exact misereOutcome_ne_P_of_pfree h_g
    · exact Or.inr rfl
  cases h_x_out : MisereOutcome x
  · exact Outcome.L_ge (MisereOutcome (g + x))
  · obtain h_g_out | h_g_out := h_g_out
    · rw [misereOutcome_N_isEnd_NN h_g h_x h_g_isEnd h_g_out h_x_out]
    · have := OutcomeStable.miserePlayerOutcome_of_add_RN h_g h_x h_g_out h_x_out
      unfold MisereOutcome Outcome.ofPlayers
      cases MiserePlayerOutcome (g + x) Player.left
      · simp [this]
      · simp [this]
  · absurd h_x_out
    exact misereOutcome_ne_P_of_pfree h_x
  · have := misereOutcome_R_add_isEnd_right h_x h_g h_x_out h_g_isEnd
    rw [add_comm] at this
    rw [this]

theorem reduction_plug_end_not_isEnd_left
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g : GameForm.{u}} (h_g : (PFreeSubset U) g)
    (h_isEnd : IsEnd .right g) (h_not_left : ¬ IsEnd .left g) :
    g =m (PFreeSubset U) !{(moves .left g) | {1}} := by
  refine MisereEq.of_antisymm ?_ ?_
  · refine Hereditary.misereGE_of_maintenance_proviso (PFreeSubset U) ?_ ?_ ?_ ?_
    · intro gr hgr
      rw [isEnd_def] at h_isEnd
      rw [h_isEnd] at hgr
      simp only [Set.mem_empty_iff_false] at hgr
    · intro hl hhl
      rw [leftMoves_ofSets] at hhl
      exact Or.inl ⟨hl, hhl, MisereGE.refl hl⟩
    · intro _hend y hy hy_end
      refine winsGoingFirst_of_moves ⟨1 + y, ?_, ?_⟩
      · rw [moves_add]
        apply Set.mem_union_left
        simp only [rightMoves_ofSets, Set.image_singleton, Set.mem_singleton_iff]
      · have := misereOutcome_R_add_isEnd_right (HasNat.one) hy one_misereOutcome_R (isEndLike_iff_isEnd.mp hy_end)
        exact (misereOutcome_R_iff_winsGoingFirst.mp this).right
    · intro hend
      exfalso
      rw [isEndLike_iff_isEnd, isEnd_def] at hend
      rw [leftMoves_ofSets] at hend
      rw [isEnd_def] at h_not_left
      exact h_not_left hend
  · refine Hereditary.misereGE_of_maintenance_proviso (PFreeSubset U) ?_ ?_ ?_ ?_
    · intro hr hhr
      rw [rightMoves_ofSets, Set.mem_singleton_iff] at hhr
      subst hhr
      apply Or.inr
      have h_out : 0 ≥m (PFreeSubset U) g := not_right_end_zero_ge h_g h_isEnd
      simpa using h_out
    · intro gl hgl
      refine Or.inl ⟨gl, ?_, MisereGE.refl gl⟩
      rwa [leftMoves_ofSets]
    · intro hend
      exfalso
      rw [isEndLike_iff_isEnd, isEnd_def] at hend
      absurd hend
      simp only [rightMoves_ofSets, Set.singleton_ne_empty, not_false_eq_true]
    · intro hend
      exact absurd (isEndLike_iff_isEnd.mp hend) h_not_left

/--
Left/Right mirror of `plugged_mem`, for a `g` that is a Left end but not a Right end.
-/
theorem pluggedLeft_mem
    {A : GameForm → Prop} [ShortUniverse A] [Blocking A] [OutcomeStable A] [HasInt A] [Short A]
    {g : GameForm} (h_g : (PFreeSubset A) g) (h_not_right : ¬ IsEnd .right g) :
    PFreeSubset A (!{{(-1 : GameForm)} | (moves .right g)}) := by
  have h_neg_not_left : ¬ IsEnd .left (-g) := by
    rw [IsEnd.neg_iff_neg]; simpa using h_not_right
  have h_mem_neg := ClosedUnderNeg.neg_of (plugged_mem (ClosedUnderNeg.neg_of h_g) h_neg_not_left)
  simp only [Plugged, neg_ofSets, Set.neg_singleton, moves_neg, neg_neg] at h_mem_neg
  exact h_mem_neg

/--
Left/Right mirror of `reduction_plug_end_not_isEnd_left`, for a `g` that is a Left end but not a
Right end.
-/
theorem reduction_plug_end_not_isEnd_right
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g : GameForm.{u}} (h_g : (PFreeSubset U) g)
    (h_isEnd : IsEnd .left g) (h_not_right : ¬ IsEnd .right g) :
    g =m (PFreeSubset U) !{{(-1 : GameForm)} | (moves .right g)} := by
  have h_neg_isEnd : IsEnd .right (-g) := by rw [IsEnd.neg_iff_neg]; simpa using h_isEnd
  have h_neg_not_left : ¬ IsEnd .left (-g) := by rw [IsEnd.neg_iff_neg]; simpa using h_not_right
  have heq := reduction_plug_end_not_isEnd_left (ClosedUnderNeg.neg_of h_g) h_neg_isEnd h_neg_not_left
  rw [<-neg_neg (!{(moves .left (-g)) | ({1} : Set GameForm)} : GameForm), misereEQ_neg_iff] at heq
  simp only [neg_ofSets, Set.neg_singleton, moves_neg, neg_neg] at heq
  exact heq

end Blocking

end GameForm

namespace PFree

/-! ## Separation -/

theorem rightSeparating_of_leftSeparating
    {A : GameForm → Prop} [Short A] [ClosedUnderDicotic IsShort A] [HasInt A]
    {g h : GameForm} (h_h : IsShort h) (h_left : AreLeftSeparating (PFreeSubset A) g h) :
    AreRightSeparating (PFreeSubset A) g h := by
  obtain ⟨x, h_x_pf, h_not_wins_left, h_wins_left⟩ := h_left
  set L : Set GameForm :=
    Set.range (fun r : moves .right h => (-((LTippingPoint (Hereditary.of_mem_moves h_h r.prop)))))
    ∪ {((-1 : ℤ) : GameForm)} with h_L_def
  have h_conj_one_mem : ((-1 : ℤ) : GameForm) ∈ L := Set.mem_union_right _ (Set.mem_singleton _)
  have h_x_mem : x ∈ moves .right (!{L | {x}} : GameForm) := by simp
  have := (misereOutcome_L_intCast_iff (G := GameForm) (-1)).mpr (by decide)
  have h_not_wins_right : ¬ WinsGoingFirst .right (((-1 : ℤ) : GameForm)) :=
    (misereOutcome_L_iff_winsGoingFirst.mp this).2
  refine ⟨!{L | {x}}, ?_, ?_, ?_⟩
  · apply pfreeSubset_short_ofSets
    · intro a h_a_mem
      rw [h_L_def] at h_a_mem
      rcases h_a_mem with ⟨r, rfl⟩ | rfl
      · exact HasInt.has_neg_int (A := PFreeSubset A) _
      · exact HasInt.has_int (A := PFreeSubset A) (-1)
    · intro a h_a_mem
      rw [Set.mem_singleton_iff] at h_a_mem
      subst h_a_mem
      exact h_x_pf
    · exact ⟨_, h_conj_one_mem⟩
    · rw [h_L_def]
      have := IsShort.finite_moves' .right h_h
      simp [Set.finite_range]
    · exact ⟨x, Set.mem_singleton x⟩
    · exact Set.finite_singleton x
    · intro h_outcome_P
      rw [misereOutcome_P_iff_winsGoingFirst' (p := .left)] at h_outcome_P
      refine h_outcome_P.left (winsGoingFirst_of_moves ⟨((-1 : ℤ) : GameForm), ?_, ?_⟩)
      · rwa [leftMoves_ofSets]
      · rwa [Player.neg_left]
  · refine winsGoingFirst_of_moves ⟨g + x, add_left_mem_moves_add h_x_mem g, ?_⟩
    rwa [Player.neg_right]
  · rw [not_winsGoingFirst_iff]
    refine ⟨?_, ?_⟩
    · simp [isEnd_def]
    · intro k h_k_mem
      rw [moves_add] at h_k_mem
      rw [Player.neg_right]
      rcases h_k_mem with ⟨h_r, h_r_mem, rfl⟩ | ⟨r, h_r_mem, rfl⟩
      · apply winsGoingFirst_of_moves
        use h_r + (-(LTippingPoint (Hereditary.of_mem_moves h_h h_r_mem)))
        constructor
        · apply add_left_mem_moves_add
          rw [leftMoves_ofSets, h_L_def]
          exact Set.mem_union_left _ ⟨⟨h_r, h_r_mem⟩, rfl⟩
        · rw [Player.neg_left]
          have := LTippingPoint_spec (Hereditary.of_mem_moves h_h h_r_mem)
          rw [misereOutcome_L_iff_winsGoingFirst] at this
          exact this.right
      · rw [rightMoves_ofSets, Set.mem_singleton_iff] at h_r_mem
        subst h_r_mem
        exact h_wins_left

/--
$(G, H)$ are Right $\operatorname{pf}(\mathcal{A})$-separated if and only if
$(G, H)$ are Left $\operatorname{pf}(\mathcal{A})$-separated.
-/
theorem rightSeparating_iff_leftSeparating
    {A : GameForm → Prop} [Short A] [ClosedUnderDicotic IsShort A] [HasInt A] [ClosedUnderNeg A]
    {g h : GameForm} (h_g : IsShort g) (h_h : IsShort h) :
    AreRightSeparating (PFreeSubset A) g h ↔ AreLeftSeparating (PFreeSubset A) g h := by
  constructor
  · intro h_right
    have h1 := Separation.leftSeparating_neg_of_rightSeparating h_right
    have h2 := rightSeparating_of_leftSeparating
      (ClosedUnderNeg.neg_of h_g) h1
    simpa using Separation.leftSeparating_neg_of_rightSeparating h2
  · exact rightSeparating_of_leftSeparating h_h

theorem separating_pair_of_right_iff_left
    {A : GameForm → Prop} [Short A] [ClosedUnderDicotic IsShort A] [HasInt A] [ClosedUnderNeg A]
    {g h : GameForm} (h_g : IsShort g) (h_h : IsShort h)
    (h_not_ge : ¬g ≥m (PFreeSubset A) h) :
    AreLeftSeparating (PFreeSubset A) g h ∧ AreRightSeparating (PFreeSubset A) g h := by
  rcases not_misereGE_iff_separating.mp h_not_ge with h_left | h_right
  · rw [rightSeparating_iff_leftSeparating h_g h_h]
    exact ⟨h_left, h_left⟩
  · rw [<-rightSeparating_iff_leftSeparating h_g h_h]
    exact ⟨h_right, h_right⟩

instance {A : GameForm → Prop}
         [Short A] [ClosedUnderDicotic IsShort A] [ClosedUnderNeg A] [HasInt A] :
         Separating IsShort (PFreeSubset A) where
  separating_pair_of_not_misereGE := separating_pair_of_right_iff_left

/-! ## Downlinking -/

theorem downlinked_of_not_isEnd_left
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    {g h : GameForm.{u}} (h_g : (PFreeSubset U) g) (h_h : (PFreeSubset U) h)
    (h_g_not_isEnd : ¬ IsEnd .left g)
    (h_moves_g : ∀ gl ∈ moves .left g, ¬ (gl ≥m (PFreeSubset U) h))
    (h_moves_h : ∀ hr ∈ moves .right h, ¬ (g ≥m (PFreeSubset U) hr)) :
    Downlinked (PFreeSubset U) g h := by
  classical
  let x' := fun gl : moves .left g => Classical.choose
    ((Separating.separating_pair_of_not_misereGE
      (IsShort.of_mem_moves (Short.isShort h_g) gl.prop) (Short.isShort h_h)
      (h_moves_g gl gl.prop)).left)
  let y' := fun hr : moves .right h => Classical.choose
    ((Separating.separating_pair_of_not_misereGE
      (Short.isShort h_g) (IsShort.of_mem_moves (Short.isShort h_h) hr.prop)
      (h_moves_h hr hr.prop)).right)
  let x (gl : GameForm) (h_gl_mem : gl ∈ moves .left g) := x' ⟨gl, h_gl_mem⟩
  let y (hr : GameForm) (h_hr_mem : hr ∈ moves .right h) := y' ⟨hr, h_hr_mem⟩
  have h_x_spec (gl : GameForm) (h_gl_mem : gl ∈ moves .left g) :
      (PFreeSubset U) (x gl h_gl_mem) ∧
        ¬WinsGoingFirst .left (gl + x gl h_gl_mem) ∧
        WinsGoingFirst .left (h + x gl h_gl_mem) := by
    simpa [x, x'] using
      (Classical.choose_spec ((Separating.separating_pair_of_not_misereGE
        (IsShort.of_mem_moves (Short.isShort h_g) h_gl_mem) (Short.isShort h_h)
        (h_moves_g gl h_gl_mem)).left))
  have h_y_spec (hr : GameForm) (h_hr_mem : hr ∈ moves .right h) :
      (PFreeSubset U) (y hr h_hr_mem) ∧
        WinsGoingFirst .right (g + y hr h_hr_mem) ∧
        ¬WinsGoingFirst .right (hr + y hr h_hr_mem) := by
    simpa [y, y'] using
      (Classical.choose_spec ((Separating.separating_pair_of_not_misereGE
        (Short.isShort h_g) (IsShort.of_mem_moves (Short.isShort h_h) h_hr_mem)
        (h_moves_h hr h_hr_mem)).right))
  have h_x_mem gl hgl := (h_x_spec gl hgl).1
  have h_x_g_win gl hgl := (h_x_spec gl hgl).2.1
  have h_x_h_win gl hgl := (h_x_spec gl hgl).2.2
  have h_y_mem hr hhr := (h_y_spec hr hhr).1
  have h_y_g_win hr hhr := (h_y_spec hr hhr).2.1
  have h_y_h_win hr hhr := (h_y_spec hr hhr).2.2
  set R : Set GameForm.{u} := Set.range x' with hRset_def
  set condSet : Set GameForm.{u} :=
    (if MisereOutcome (g + ((-1 : ℤ) : GameForm)) = .L then
        (if IsEnd .right h then {((RTippingPoint (Short.isShort h_g) : ℤ) : GameForm)} else ∅)
      else {((-1 : ℤ) : GameForm)}) with hcondSet_def
  set L : Set GameForm.{u} := condSet ∪ Set.range y' with hLset_def

  haveI hSmallR : Small.{u} R := by rw [hRset_def]; infer_instance
  haveI hSmallCond : Small.{u} condSet := by
    rw [hcondSet_def]
    split
    · split <;> infer_instance
    · infer_instance
  haveI hSmallL : Small.{u} L := by rw [hLset_def]; infer_instance

  use !{L|R}
  refine ⟨?_, ?_, ?_⟩
  · apply pfreeSubset_short_ofSets
    · rw [hLset_def]
      rintro w (hw | ⟨hr, rfl⟩)
      · rw [hcondSet_def] at hw
        split at hw
        · split at hw
          · rw [Set.mem_singleton_iff] at hw; subst hw; exact HasInt.has_int _
          · simp at hw
        · rw [Set.mem_singleton_iff] at hw; subst hw; exact HasInt.has_int _
      · exact h_y_mem _ _
    · rintro r ⟨gl, rfl⟩
      exact h_x_mem _ _
    · rw [hLset_def]
      by_cases hout : MisereOutcome (g + ((-1 : ℤ) : GameForm)) = .L
      · by_cases hend : IsEnd .right h
        · refine ⟨((RTippingPoint (Short.isShort h_g) : ℤ) : GameForm), Set.mem_union_left _ ?_⟩
          rw [hcondSet_def, if_pos hout, if_pos hend]; exact Set.mem_singleton _
        · obtain ⟨hr, h_hr_mem⟩ := not_isEnd_exists_move hend
          exact ⟨_, Set.mem_union_right _ ⟨⟨hr, h_hr_mem⟩, rfl⟩⟩
      · refine ⟨((-1 : ℤ) : GameForm), Set.mem_union_left _ ?_⟩
        rw [hcondSet_def, if_neg hout]; exact Set.mem_singleton _
    · rw [hLset_def]
      apply Set.Finite.union
      · rw [hcondSet_def]
        split
        · split
          · exact Set.finite_singleton _
          · exact Set.finite_empty
        · exact Set.finite_singleton _
      · have : Finite (moves .right h) := IsShort.finite_moves' .right (Short.isShort h_h)
        exact Set.finite_range _
    · obtain ⟨gl, h_gl_mem⟩ := not_isEnd_exists_move h_g_not_isEnd
      exact ⟨_, ⟨⟨gl, h_gl_mem⟩, rfl⟩⟩
    · rw [hRset_def]
      have : Finite (moves .left g) := IsShort.finite_moves' .left (Short.isShort h_g)
      exact Set.finite_range _
    · rw [misereOutcome_ne_P_iff_winsGoingFirst]
      by_cases hout : MisereOutcome (g + ((-1 : ℤ) : GameForm)) = .L
      · apply Or.inl
        obtain ⟨gl, h_gl_mem, h_gl_ge_zero⟩ :=
          OutcomeStable.exists_leftMove_misereGE_zero_of_misereOutcome_add_neg_one_L
            h_g h_g_not_isEnd hout
        refine winsGoingFirst_of_moves ⟨x gl h_gl_mem, ?_, ?_⟩
        · rw [rightMoves_ofSets]
          exact ⟨⟨gl, h_gl_mem⟩, rfl⟩
        · rw [Player.neg_right]
          intro hh
          exact h_x_g_win gl h_gl_mem
            (winsGoingFirst_left_add_of_misereGE_zero (h_x_mem gl h_gl_mem) h_gl_ge_zero hh)
      · apply Or.inr
        refine winsGoingFirst_of_moves ⟨((-1 : ℤ) : GameForm), ?_, ?_⟩
        · rw [leftMoves_ofSets, hLset_def]
          refine Set.mem_union_left _ ?_
          rw [hcondSet_def, if_neg hout]
          exact Set.mem_singleton _
        · rw [← winsGoingFirst_neg_iff]
          simp
  · rw [not_winsGoingFirst_iff]
    refine ⟨?_, ?_⟩
    · rw [GameForm.isEndLike_iff_isEnd, IsEnd.add_iff]
      intro h1
      exact h_g_not_isEnd h1.left
    · intro gtl h_gtl_mem
      rw [moves_add] at h_gtl_mem
      rw [Player.neg_left]
      rcases h_gtl_mem with ⟨gl, h_gl_mem, rfl⟩ | ⟨tl, h_tl_mem, rfl⟩
      · refine winsGoingFirst_of_moves ⟨gl + x gl h_gl_mem, ?_, ?_⟩
        · apply add_left_mem_moves_add
          simp
          exact ⟨⟨gl, h_gl_mem⟩, rfl⟩
        · rw [Player.neg_right]
          exact h_x_g_win gl h_gl_mem
      · simp [hLset_def] at h_tl_mem
        rcases h_tl_mem with hw | ⟨tr, h_tr_mem, rfl⟩
        · rw [hcondSet_def] at hw
          split at hw
          next h_eq =>
            split at hw
            · rw [Set.mem_singleton_iff] at hw; subst hw
              have hR : MisereOutcome (g + ((RTippingPoint (Short.isShort h_g) : ℕ) : GameForm)) = .R :=
                misereOutcome_add_RTippingPoint_R (Short.isShort h_g)
              have hcast : (((RTippingPoint (Short.isShort h_g) : ℤ)) : GameForm)
                  = ((RTippingPoint (Short.isShort h_g) : ℕ) : GameForm) := by simp
              rw [hcast]
              exact (misereOutcome_R_iff_winsGoingFirst.mp hR).left
            · simp at hw
          next h_ne =>
            rw [Set.mem_singleton_iff] at hw; subst hw
            cases ho : MisereOutcome (g + ((-1 : ℤ) : GameForm)) with
            | L => exact absurd ho h_ne
            | P => exact absurd ho (OutcomeStable.misereOutcome_add_int_ne_P h_g (-1))
            | N => exact (misereOutcome_N_iff_winsGoingFirst.mp ho).right
            | R => exact (misereOutcome_R_iff_winsGoingFirst.mp ho).left
        · exact h_y_g_win _ _
  · rw [not_winsGoingFirst_iff]
    refine ⟨?_, ?_⟩
    · rw [GameForm.isEndLike_iff_isEnd, IsEnd.add_iff]
      simp [isEnd_def, hRset_def]
      intro _
      exact (not_isEnd_def Player.left g).mp h_g_not_isEnd
    · intro htr h_htr_mem
      rw [moves_add] at h_htr_mem
      rw [Player.neg_right]
      rcases h_htr_mem with ⟨hr, h_hr_mem, rfl⟩ | ⟨tr, h_tr_mem, rfl⟩
      · refine winsGoingFirst_of_moves ⟨hr + y hr h_hr_mem, ?_, ?_⟩
        · apply add_left_mem_moves_add
          rw [leftMoves_ofSets, hLset_def]
          exact Set.mem_union_right _ ⟨⟨hr, h_hr_mem⟩, rfl⟩
        · rw [Player.neg_left]
          exact h_y_h_win hr h_hr_mem
      · rw [rightMoves_ofSets] at h_tr_mem
        obtain ⟨⟨gl, h_gl_mem⟩, rfl⟩ := h_tr_mem
        exact h_x_h_win gl h_gl_mem

theorem downlinked_of_not_isEnd_right
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    {g h : GameForm} (h_g : (PFreeSubset U) g) (h_h : (PFreeSubset U) h)
    (h_h_not_isEnd : ¬ IsEnd .right h)
    (h_moves_g : ∀ gl ∈ moves .left g, ¬ (gl ≥m (PFreeSubset U) h))
    (h_moves_h : ∀ hr ∈ moves .right h, ¬ (g ≥m (PFreeSubset U) hr)) :
    Downlinked (PFreeSubset U) g h := by
  rw [←Downlinked.neg_iff]
  apply downlinked_of_not_isEnd_left (ClosedUnderNeg.neg_of h_h) (ClosedUnderNeg.neg_of h_g)
  · rw [IsEnd.neg_iff_neg]
    simpa using h_h_not_isEnd
  · intro hl h_hl_neg_mem h_hl_ge
    rw [moves_neg, Set.mem_neg] at h_hl_neg_mem
    have := h_moves_h (-hl) h_hl_neg_mem
    exact this ((ClosedUnderNeg.neg_ge_neg_iff g (-hl)).mp (by rwa [neg_neg]))
  · intro gr h_gr_neg_mem h_gr_ge
    rw [moves_neg, Set.mem_neg] at h_gr_neg_mem
    have := h_moves_g (-gr) h_gr_neg_mem
    exact this ((ClosedUnderNeg.neg_ge_neg_iff (-gr) h).mp (by rwa [neg_neg]))

theorem downlinked_intCast_of_not_leftMoves_misereGE
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    {g : GameForm} {n : ℤ}
    (h_g : (PFreeSubset U) g) (h_not_left_end : ¬ IsEnd .left g) (h_n : 0 ≤ n)
    (h : ∀ gl ∈ moves .left g, ¬ (gl ≥m (PFreeSubset U) ((n : ℤ) : GameForm))) :
    Form.Downlinked (PFreeSubset U) g ((n : ℤ) : GameForm) := by
  apply downlinked_of_not_isEnd_left (g := g) (h := n) h_g (HasInt.has_int n) h_not_left_end h
  simp [h_n]

theorem misereGE_iff_promain_not_isEnd_left_right
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U]
    {g h : GameForm}
    (h_g : (PFreeSubset U) g) (h_h : (PFreeSubset U) h)
    (h_g_not_isEnd : ¬ IsEnd .left g) (h_h_not_isEnd : ¬ IsEnd .right h) :
    g ≥m (PFreeSubset U) h ↔ Promain.Test (PFreeSubset U) g h := by
  constructor
  · intro hge
    refine ⟨?_, ?_, proviso_right_of_misereGE hge, proviso_left_of_misereGE hge⟩
    · intro gr h_gr_mem
      by_contra h_not
      push_neg at h_not
      obtain ⟨h_no_hr, h_no_grl⟩ := h_not
      have h_dl := downlinked_of_not_isEnd_right (Hereditary.of_mem_moves h_g h_gr_mem)
        h_h h_h_not_isEnd h_no_grl h_no_hr
      exact not_downlinked_right_option_of_misereGE hge h_gr_mem h_dl
    · intro hl h_hl_mem
      by_contra h_not
      push_neg at h_not
      obtain ⟨h_no_gl, h_no_hlr⟩ := h_not
      have h_dl := downlinked_of_not_isEnd_left h_g (Hereditary.of_mem_moves h_h h_hl_mem)
        h_g_not_isEnd h_no_gl h_no_hlr
      exact not_downlinked_left_option_of_misereGE hge h_hl_mem h_dl
  · intro ⟨h1, h2, h3, h4⟩
    exact Hereditary.misereGE_of_maintenance_proviso (PFreeSubset U) h1 h2 h3 h4

private lemma maintenance_of_misereGE_int_left
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    {g : GameForm} {n : ℤ} (h_n : 0 ≤ n)
    (h_g : (PFreeSubset U) g) (g_not_end : ¬IsEnd .left g)
    (h_ge : g ≥m (PFreeSubset U) (n : ℤ)) :
    Maintenance (PFreeSubset U) g !{{((n - 1 : ℤ) : GameForm)} | {1}} .left := by
  intro hl h_hl_mem
  rw [leftMoves_ofSets, Set.mem_singleton_iff] at h_hl_mem
  subst h_hl_mem
  rcases h_n.lt_or_eq with h_zero_lt | rfl
  · apply Or.inl
    by_contra h_contra
    push_neg at h_contra
    have h_downlinked :=
      downlinked_intCast_of_not_leftMoves_misereGE (n := n - 1) h_g g_not_end (by omega) h_contra
    have h_mem : ((n - 1 : ℤ) : GameForm) ∈ moves .left ((n : ℤ) : GameForm) :=
      leftMoves_intCast_zero_lt h_zero_lt
    absurd h_downlinked
    exact Form.not_downlinked_left_option_of_misereGE h_ge h_mem
  · apply Or.inr
    refine ⟨(0 : GameForm), ?_, ?_⟩
    · simp
    · simpa using h_ge

private lemma maintenance_of_misereGE_int_right
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U]
    {g : GameForm} {n : ℤ} (h_n : 0 ≤ n)
    (h_g : (PFreeSubset U) g) (h_ge : g ≥m (PFreeSubset U) (n : ℤ)) :
    Maintenance (PFreeSubset U) g !{{((n - 1 : ℤ) : GameForm)} | {1}} .right := by
  intro gr h_gr_mem
  by_contra h_contra
  push_neg at h_contra
  have h_gr_pf : (PFreeSubset U) gr := Hereditary.of_mem_moves h_g h_gr_mem
  have h_one_mem : (1 : GameForm) ∈ moves .right !{{((n - 1 : ℤ) : GameForm)} | {1}} := by
    simp
  have h_not_ge_one : ¬ (gr ≥m (PFreeSubset U) (1 : GameForm)) := h_contra.left 1 h_one_mem
  have h_downlinked : Downlinked (PFreeSubset U) gr ((n : ℤ) : GameForm) := by
    by_cases h_end : IsEnd .left gr
    · apply downlinked_of_downlinked_misereEQ_right (IntegerInvertible.reduction_pred_intCast_slash_one (A := U) h_n)
      refine downlinked_of_not_isEnd_right h_gr_pf ?_ ?_ ?_ ?_
      · exact OutcomeStable.intSlashOne_mem (A := U) (n := n - 1) (by omega)
      · rw [isEnd_def, rightMoves_ofSets]
        exact Set.singleton_ne_empty _
      · intro grl hgrl
        rw [isEnd_def] at h_end
        rw [h_end] at hgrl
        simp at hgrl
      · intro hr hhr
        rw [rightMoves_ofSets, Set.mem_singleton_iff] at hhr
        subst hhr
        exact h_not_ge_one
    · refine downlinked_intCast_of_not_leftMoves_misereGE (n := n) h_gr_pf h_end h_n ?_
      intro grl hgrl h_gl_ge
      rw [<-misereGE_rw_right_iff (IntegerInvertible.reduction_pred_intCast_slash_one h_n)] at h_gl_ge
      exact h_contra.right grl hgrl h_gl_ge
  exact (Form.not_downlinked_right_option_of_misereGE h_ge h_gr_mem) h_downlinked

theorem misereGE_iff_promain_not_isEnd_left_int
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U]
    {g : GameForm} {n : ℤ} (h_n : 0 ≤ n)
    (h_g : (PFreeSubset U) g) (h_g_not_isEnd : ¬IsEnd .left g) :
    (g ≥m (PFreeSubset U) (n : ℤ) ↔
      (Promain.Test (PFreeSubset U) g !{{((n - 1 : ℤ) : GameForm)} | {1}})) := by
  constructor
  · intro h_ge
    unfold Promain.Test
    have := (misereGE_rw_right_iff (IntegerInvertible.reduction_pred_intCast_slash_one h_n)).mpr h_ge
    exact ⟨ maintenance_of_misereGE_int_right h_n h_g h_ge
          , maintenance_of_misereGE_int_left h_n h_g h_g_not_isEnd h_ge
          , proviso_right_of_misereGE this
          , proviso_left_of_misereGE this
          ⟩
  · intro ⟨h1, h2, h3, h4⟩
    have := MisereEQ.symm (IntegerInvertible.reduction_pred_intCast_slash_one (A := U) h_n)
    rw [misereGE_rw_right_iff this]
    refine Hereditary.misereGE_of_maintenance_proviso (PFreeSubset U) h1 h2 h3 h4

private lemma maintenance_of_misereGE_not_isEnd_left_left
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U] [Blocking U]
    {g h : GameForm} (h_g : (PFreeSubset U) g) (h_h : (PFreeSubset U) h)
    (g_not_end : ¬IsEnd .left g)
    (h_ge : g ≥m (PFreeSubset U) h) :
    Maintenance (PFreeSubset U) g h .left := by
  intro hl h_hl_mem
  by_contra h_absurd
  push_neg at h_absurd
  have h_downlinked := downlinked_of_not_isEnd_left h_g (Hereditary.of_mem_moves h_h h_hl_mem) g_not_end h_absurd.left h_absurd.right
  absurd h_downlinked
  exact Form.not_downlinked_left_option_of_misereGE h_ge h_hl_mem

theorem misereGE_iff_promain_not_isEnd_left_left
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g h : GameForm}
    (h_g : (PFreeSubset U) g) (h_h : (PFreeSubset U) h)
    (h_g_not_isEnd : ¬ IsEnd .left g) (h_h_not_isEnd : ¬ IsEnd .left h) (h_h_isEnd : IsEnd .right h) :
    g ≥m (PFreeSubset U) h ↔ Promain.Test (PFreeSubset U) g !{(moves .left h) | {1}} := by
  have h_h_out := Blocking.not_right_end_zero_ge h_h h_h_isEnd
  have h_h_eq_plugged := Blocking.reduction_plug_end_not_isEnd_left h_h h_h_isEnd h_h_not_isEnd
  constructor
  · intro hge
    have hge' := (misereGE_rw_right_iff h_h_eq_plugged.symm).mpr hge
    refine ⟨?_, ?_, proviso_right_of_misereGE hge', proviso_left_of_misereGE hge'⟩
    · intro gr h_gr_mem
      by_contra h_not
      push_neg at h_not
      obtain ⟨h_no_hr, h_no_grl⟩ := h_not
      have not_gr_ge_one := h_no_hr 1 (by simp)
      have := downlinked_of_not_isEnd_right
                (Hereditary.of_mem_moves h_g h_gr_mem) (Blocking.plugged_mem h_h h_h_not_isEnd)
                (by simp [Blocking.Plugged, isEnd_def]) ?_ ?_
      · have := downlinked_of_downlinked_misereEQ_right h_h_eq_plugged.symm this
        exact not_downlinked_right_option_of_misereGE hge h_gr_mem this
      · intro grl h_grl_mem h_contra
        exact (h_no_grl grl h_grl_mem) h_contra
      · intro hr h_hr_mem h_contra
        rw [rightMoves_ofSets, Set.mem_singleton_iff] at h_hr_mem; subst h_hr_mem
        exact not_gr_ge_one h_contra
    · intro hl h_hl_mem
      rw [leftMoves_ofSets] at h_hl_mem
      by_contra h_not
      push_neg at h_not
      obtain ⟨h_no_gl, h_no_hlr⟩ := h_not
      have h_dl := downlinked_of_not_isEnd_left h_g (Hereditary.of_mem_moves h_h h_hl_mem)
        h_g_not_isEnd h_no_gl h_no_hlr
      exact not_downlinked_left_option_of_misereGE hge h_hl_mem h_dl
  · intro ⟨h1, h2, h3, h4⟩
    rw [misereGE_rw_right_iff h_h_eq_plugged]
    exact (Hereditary.misereGE_of_maintenance_proviso (PFreeSubset U) h1 h2 h3 h4)

theorem misereGE_iff_promain_not_isEnd_right_right
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g h : GameForm}
    (h_g : (PFreeSubset U) g) (h_h : (PFreeSubset U) h)
    (h_g_isEnd : IsEnd .left g) (h_g_not_isEnd : ¬ IsEnd .right g) (h_h_not_isEnd : ¬ IsEnd .right h) :
    g ≥m (PFreeSubset U) h ↔
      Promain.Test (PFreeSubset U) !{{(-1 : GameForm)} | (moves .right g)} h := by
  have h_g_eq_plugged := Blocking.reduction_plug_end_not_isEnd_right h_g h_g_isEnd h_g_not_isEnd
  have h_g_plugged_mem := Blocking.pluggedLeft_mem h_g h_g_not_isEnd
  have h_g_plugged_not_left :
      ¬ IsEnd .left (!{{(-1 : GameForm)} | (moves .right g)} : GameForm) := by
    simp [isEnd_def]
  constructor
  · intro hge
    rwa [<-misereGE_iff_promain_not_isEnd_left_right h_g_plugged_mem h_h h_g_plugged_not_left h_h_not_isEnd,
         <-misereGE_rw_left_iff h_g_eq_plugged]
  · intro htest
    rwa [misereGE_rw_left_iff h_g_eq_plugged,
         misereGE_iff_promain_not_isEnd_left_right h_g_plugged_mem h_h h_g_plugged_not_left h_h_not_isEnd]

theorem misereGE_iff_promain_not_isEnd_right_int
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g : GameForm} {n : ℤ} (h_n : 0 ≤ n)
    (h_g : (PFreeSubset U) g)
    (h_g_isEnd : IsEnd .left g) (h_g_not_isEnd : ¬ IsEnd .right g) :
    (g ≥m (PFreeSubset U) (n : ℤ) ↔
      (Promain.Test (PFreeSubset U) !{{(-1 : GameForm)} | (moves .right g)}
        !{{((n - 1 : ℤ) : GameForm)} | {1}})) := by
  have h_g_eq_plugged := Blocking.reduction_plug_end_not_isEnd_right h_g h_g_isEnd h_g_not_isEnd
  have h_g_plugged_mem := Blocking.pluggedLeft_mem h_g h_g_not_isEnd
  have h_g_plugged_not_left :
      ¬ IsEnd .left (!{{(-1 : GameForm)} | (moves .right g)} : GameForm) := by
    simp [isEnd_def]
  constructor
  · intro hge
    rwa [<-misereGE_iff_promain_not_isEnd_left_int h_n h_g_plugged_mem h_g_plugged_not_left,
        <-misereGE_rw_left_iff h_g_eq_plugged]
  · intro htest
    rwa [misereGE_rw_left_iff h_g_eq_plugged,
         misereGE_iff_promain_not_isEnd_left_int h_n h_g_plugged_mem h_g_plugged_not_left]

theorem misereGE_iff_promain_not_isEnd_right_left
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g h : GameForm}
    (h_g : (PFreeSubset U) g) (h_h : (PFreeSubset U) h)
    (h_g_isEnd : IsEnd .left g) (h_g_not_isEnd : ¬ IsEnd .right g)
    (h_h_not_isEnd : ¬ IsEnd .left h) (h_h_isEnd : IsEnd .right h) :
    g ≥m (PFreeSubset U) h ↔
      Promain.Test (PFreeSubset U) !{{(-1 : GameForm)} | (moves .right g)} !{(moves .left h) | {1}} := by
  have h_g_eq_plugged := Blocking.reduction_plug_end_not_isEnd_right h_g h_g_isEnd h_g_not_isEnd
  have h_g_plugged_mem := Blocking.pluggedLeft_mem h_g h_g_not_isEnd
  have h_g_plugged_not_left :
      ¬ IsEnd .left (!{{(-1 : GameForm)} | (moves .right g)} : GameForm) := by
    simp [isEnd_def]
  constructor
  · intro hge
    rwa [<-misereGE_iff_promain_not_isEnd_left_left h_g_plugged_mem h_h h_g_plugged_not_left h_h_not_isEnd h_h_isEnd,
         <-misereGE_rw_left_iff h_g_eq_plugged]
  · intro htest
    rwa [misereGE_rw_left_iff h_g_eq_plugged,
         misereGE_iff_promain_not_isEnd_left_left h_g_plugged_mem h_h h_g_plugged_not_left h_h_not_isEnd h_h_isEnd]

theorem misereGE_iff_promain_zero_left
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    {h : GameForm} (h_h : ∀ hl ∈ moves .left h, (PFreeSubset U) hl)
    (h_h_left_not_end : ∀ hl ∈ moves .left h, ¬ IsEnd .right hl) :
    (0 : GameForm) ≥m (PFreeSubset U) h ↔ Promain.Test (PFreeSubset U) 0 h := by
  constructor
  · intro hge
    refine ⟨?_, ?_, proviso_right_of_misereGE hge, proviso_left_of_misereGE hge⟩
    · intro gr h_gr_mem
      simp only [moves_zero, Set.mem_empty_iff_false] at h_gr_mem
    · intro hl h_hl_mem
      by_contra h_not
      push_neg at h_not
      obtain ⟨_, h_no_hlr⟩ := h_not
      have h_dl := downlinked_of_not_isEnd_right HasNat.zero (h_h hl h_hl_mem)
        (h_h_left_not_end hl h_hl_mem) (by simp [moves_zero]) h_no_hlr
      exact not_downlinked_left_option_of_misereGE hge h_hl_mem h_dl
  · intro ⟨h1, h2, h3, h4⟩
    exact Hereditary.misereGE_of_maintenance_proviso (PFreeSubset U) h1 h2 h3 h4

theorem misereEQ_dropEnds_of_dominated
    {A : GameForm → Prop} [Hereditary A] [OutcomeStable A] [Short A] [ShortUniverse A] [HasInt A]
    [ClosedUnderAddNat A] [IntegerInvertible A] [Blocking A]
    {h : GameForm} (h_h : (PFreeSubset A) h)
    (h_out : MisereOutcome h = .N) :
    h =m (PFreeSubset A) !{{hl ∈ moves .left h | ¬ IsEnd .right hl} | moves .right h} := by
  apply Hereditary.misereEQ_of_left_subset_dominated
  · rw [rightMoves_ofSets]
  · rw [leftMoves_ofSets]
    exact Set.sep_subset _ _
  · rw [leftMoves_ofSets]
    intro hl h_hl_mem
    by_cases h_hl_end_right : IsEnd .right hl
    · rw [misereOutcome_N_iff_winsGoingFirst, winsGoingFirst_iff (p := .left)] at h_out
      obtain h_h_end_left | ⟨hl', h_hl'_mem, h_hl'_not_win⟩ := h_out.left
      · absurd (isEndLike_iff_isEnd.mp h_h_end_left)
        exact not_isEnd_of_mem_moves h_hl_mem
      · use hl'
        have h_hl' := Hereditary.of_mem_moves h_h h_hl'_mem
        have h_hl'_out_L : MisereOutcome hl' = .L := by
          rw [misereOutcome_L_iff_winsGoingFirst]
          refine ⟨?_, h_hl'_not_win⟩
          by_contra hc
          exact misereOutcome_ne_P_of_pfree h_hl' (misereOutcome_P_iff_winsGoingFirst.mpr ⟨h_hl'_not_win, hc⟩)
        constructor
        · simp [h_hl'_mem]
          intro h_a_end
          exact h_hl'_not_win (winsGoingFirst_of_isEnd h_a_end)
        · have h1 := Blocking.not_right_end_zero_ge (Hereditary.of_mem_moves h_h h_hl_mem) h_hl_end_right
          have h2 := OutcomeStable.misereGE_zero_of_misereOutcome_L h_hl' h_hl'_out_L
          rw [Form.intCast_zero] at h2
          exact MisereGE.trans h2 h1
    · exact ⟨hl, Set.mem_sep h_hl_mem h_hl_end_right, MisereGE.refl hl⟩

theorem misereGE_zero_iff_promain_of_misereOutcome_N
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {h : GameForm} (h_h : (PFreeSubset U) h) (h_out : MisereOutcome h = .N) :
    (0 : GameForm) ≥m (PFreeSubset U) h ↔
      Promain.Test (PFreeSubset U) 0
        !{{hl ∈ moves .left h | ¬ IsEnd .right hl} | moves .right h} := by
  have h_wins_left := (misereOutcome_N_iff_winsGoingFirst.mp h_out).left
  rw [winsGoingFirst_iff] at h_wins_left
  have h_eq := misereEQ_dropEnds_of_dominated h_h h_out
  rw [misereGE_rw_right_iff h_eq]
  apply misereGE_iff_promain_zero_left
  · intro hl h_hl
    simp only [leftMoves_ofSets, Set.mem_setOf_eq] at h_hl
    exact Hereditary.of_mem_moves h_h h_hl.left
  · intro hl h_hl
    simp only [leftMoves_ofSets, Set.mem_setOf_eq] at h_hl
    exact h_hl.right

theorem misereGE_zero_iff
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {h : GameForm} (h_h : (PFreeSubset U) h) :
    (0 : GameForm) ≥m (PFreeSubset U) h ↔
      MisereOutcome h = .R ∨
        (MisereOutcome h = .N ∧ Promain.Test (PFreeSubset U) 0
          !{{hl ∈ moves .left h | ¬ IsEnd .right hl} | moves .right h}) := by
  cases h_out : MisereOutcome h
  · constructor
    · intro hge
      exact absurd hge (not_misereGE_zero_of_misereOutcome_L h_out)
    · rintro (h1 | ⟨h1, _⟩) <;> exact absurd h1 (by decide)
  · rw [misereGE_zero_iff_promain_of_misereOutcome_N h_h h_out]
    simp
  · exact absurd h_out (misereOutcome_ne_P_of_pfree h_h)
  · exact ⟨fun _ => Or.inl rfl, fun _ => OutcomeStable.misereGE_zero_of_misereOutcome_R h_h h_out⟩

open Classical in
theorem misereGE_iff_promain
    {U : GameForm → Prop} [OutcomeStable U] [Short U] [ShortUniverse U] [HasInt U]
    [ClosedUnderAddNat U] [IntegerInvertible U] [Blocking U]
    {g h : GameForm} (h_g : (PFreeSubset U) g) (h_h : (PFreeSubset U) h) :
    g ≥m (PFreeSubset U) h ↔
      if IsEnd .left g ∧ IsEnd .right g then
        (0 : GameForm) ≥m (PFreeSubset U) h
      else
        Promain.Test (PFreeSubset U)
          (if IsEnd .left g then !{{(-1 : GameForm)} | (moves .right g)} else g)
          (if IsEnd .left h ∧ IsEnd .right h then !{{(-1 : GameForm)} | {(1 : GameForm)}}
           else if IsEnd .right h then !{(moves .left h) | {(1 : GameForm)}}
           else h) := by
  by_cases hg_both : IsEnd .left g ∧ IsEnd .right g
  · simp only [hg_both, if_true]
    exact misereGE_iff_zero_of_isEnd_left_isEnd_right hg_both.1 hg_both.2
  · simp only [hg_both, if_false]
    have hg_not_right : IsEnd .left g → ¬ IsEnd .right g := fun hl hr => hg_both ⟨hl, hr⟩
    by_cases hg_left : IsEnd .left g
    · simp only [hg_left, if_true]
      have hg_nr := hg_not_right hg_left
      by_cases hh_both : IsEnd .left h ∧ IsEnd .right h
      · simp only [hh_both, if_true]
        obtain ⟨hh_l, hh_r⟩ := hh_both
        rw [both_ends_eq_zero hh_l hh_r, <-Form.intCast_zero]
        have := misereGE_iff_promain_not_isEnd_right_int (U := U) (le_refl (0 : ℤ)) h_g hg_left hg_nr
        simpa using this
      · simp only [hh_both, if_false]
        by_cases hh_right : IsEnd .right h
        · simp only [hh_right, if_true]
          exact misereGE_iff_promain_not_isEnd_right_left h_g h_h hg_left hg_nr
            (fun hl => hh_both ⟨hl, hh_right⟩) hh_right
        · simp only [hh_right, if_false]
          exact misereGE_iff_promain_not_isEnd_right_right h_g h_h hg_left hg_nr hh_right
    · simp only [hg_left, if_false]
      by_cases hh_both : IsEnd .left h ∧ IsEnd .right h
      · simp only [hh_both, if_true]
        obtain ⟨hh_l, hh_r⟩ := hh_both
        rw [both_ends_eq_zero hh_l hh_r, <-Form.intCast_zero]
        have := misereGE_iff_promain_not_isEnd_left_int (U := U) (le_refl (0 : ℤ)) h_g hg_left
        simpa using this
      · simp only [hh_both, if_false]
        by_cases hh_right : IsEnd .right h
        · simp only [hh_right, if_true]
          exact misereGE_iff_promain_not_isEnd_left_left h_g h_h hg_left
            (fun hl => hh_both ⟨hl, hh_right⟩) hh_right
        · simp only [hh_right, if_false]
          exact misereGE_iff_promain_not_isEnd_left_right h_g h_h hg_left hh_right


end PFree
