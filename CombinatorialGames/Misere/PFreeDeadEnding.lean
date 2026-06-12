/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.DeadEnding
public import CombinatorialGames.Misere.Hereditary.MaintenanceProviso
public import CombinatorialGames.Misere.OutcomeStable
public import CombinatorialGames.Misere.PFree

public section

universe u

open Form
open Form.Misere.Outcome
open GameForm
open PFree

structure PFreeDeadEnding (g : GameForm) : Prop where
  p_free : IsPFree g
  dead_ending : IsDeadEnding g

private theorem PFreeDeadEnding_of_mem_moves {g gp : GameForm} {p : Player}
    (h : PFreeDeadEnding g) (h_mem : gp ∈ moves p g) : PFreeDeadEnding gp where
  p_free := isPFree_of_mem_moves h.p_free h_mem
  dead_ending := isDeadEnding_of_mem_moves h.dead_ending h_mem

instance : PFree PFreeDeadEnding where
  pfree h := h.p_free

instance : ClosedUnderAddNat PFreeDeadEnding where
  has_add g n :=
    { p_free := isPFree_add_natCast g.p_free n
    , dead_ending := IsDeadEnding.add g.dead_ending (isDeadEnding_natCast n)
    }

instance : ClosedUnderNeg PFreeDeadEnding where
  neg_of g :=
    { p_free := ClosedUnderNeg.neg_iff.mpr g.p_free
    , dead_ending := ClosedUnderNeg.neg_iff.mpr g.dead_ending
    }

instance : HasNat PFreeDeadEnding where
  has_nat n :=
    { p_free := isPFree_natCast n
    , dead_ending := isDeadEnding_natCast n
    }

instance : HasInt PFreeDeadEnding where
  has_int n :=
    { p_free := isPFree_intCast n
    , dead_ending := isDeadEnding_intCast n
    }

private theorem misereOutcome_of_isPFree_not_winsGoingFirst {g : GameForm}
    (h_pfree : IsPFree g) (h_not_right : ¬WinsGoingFirst .right g) : MisereOutcome g = .L := by
  rw [misereOutcome_L_iff_winsGoingFirst]
  refine ⟨?_, h_not_right⟩
  by_contra h_not_left
  exact misereOutcome_ne_P_of_pfree h_pfree (misereOutcome_P_iff_winsGoingFirst.mpr ⟨h_not_right, h_not_left⟩)

private theorem eq_zero_of_misereOutcome {g : GameForm} (hg : PFreeDeadEnding g)
    (hN : MisereOutcome g = .N) (h_left_end : IsEnd .left g) : g = 0 := by
  by_contra h_ne_zero
  have h_left_dead := isDeadEnd_of_isDeadEnding hg.dead_ending h_left_end
  exact absurd (GameForm.lemma3_L g h_ne_zero h_left_dead) (by simp [hN])

mutual

private theorem misereOutcome_of_add_LL.aux {g h : GameForm}
    (hg : PFreeDeadEnding g) (hh : PFreeDeadEnding h)
    (hgL : MisereOutcome g = .L) (hhL : MisereOutcome h = .L) :
    MisereOutcome (g + h) = .L := by
  have hg_out := misereOutcome_L_iff_winsGoingFirst.mp hgL
  have hh_out := misereOutcome_L_iff_winsGoingFirst.mp hhL
  rw [misereOutcome_L_iff_winsGoingFirst]
  constructor
  · rcases (winsGoingFirst_iff g .left).mp hg_out.left with
        hg_end | ⟨gl, hgl, hgl_not_right⟩
    · rcases (winsGoingFirst_iff h .left).mp hh_out.left with
          hh_end | ⟨hl, hhl, hhl_not_right⟩
      · exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨isEndLike_iff_isEnd.mp hg_end, isEndLike_iff_isEnd.mp  hh_end⟩)
      · have hhl_pfde := PFreeDeadEnding_of_mem_moves hh hhl
        have hhlL := misereOutcome_of_isPFree_not_winsGoingFirst hhl_pfde.p_free hhl_not_right
        have hsumL := misereOutcome_of_add_LL.aux hg hhl_pfde hgL hhlL
        exact winsGoingFirst_of_moves
          ⟨g + hl, add_left_mem_moves_add hhl g, (misereOutcome_L_iff_winsGoingFirst.mp hsumL).right⟩
    · have hgl_pfde := PFreeDeadEnding_of_mem_moves hg hgl
      have hglL := misereOutcome_of_isPFree_not_winsGoingFirst hgl_pfde.p_free hgl_not_right
      have hsumL := misereOutcome_of_add_LL.aux hgl_pfde hh hglL hhL
      exact winsGoingFirst_of_moves
        ⟨gl + h, add_right_mem_moves_add hgl h, (misereOutcome_L_iff_winsGoingFirst.mp hsumL).right⟩
  · rw [not_winsGoingFirst_iff]
    refine ⟨fun h_end => ?_, fun gr hgr => ?_⟩
    · exact hg_out.right (winsGoingFirst_of_isEnd (IsEnd.add_iff.mp (isEndLike_iff_isEnd.mp  h_end)).left)
    · rw [moves_add, Set.mem_union, Set.mem_image] at hgr
      rcases hgr with ⟨gr', hgr', rfl⟩ | ⟨hr, hhr, rfl⟩
      · have h_left_gr' : WinsGoingFirst .left gr' := by
          simpa [Player.neg_right] using
            (not_winsGoingFirst_iff.mp hg_out.right).right gr' hgr'
        have hgr_pfde := PFreeDeadEnding_of_mem_moves hg hgr'
        cases hgr'_out : MisereOutcome gr' with
        | L => exact (misereOutcome_L_iff_winsGoingFirst.mp (misereOutcome_of_add_LL.aux hgr_pfde hh hgr'_out hhL)).left
        | N => exact add_comm h gr' ▸ miserePlayerOutcome_eq_iff_winsGoingFirst.mp
                 (miserePlayerOutcome_of_add_LN.aux hh hgr_pfde hhL hgr'_out)
        | P => exact absurd hgr'_out (misereOutcome_ne_P_of_pfree hgr_pfde)
        | R => exact absurd h_left_gr' (misereOutcome_R_iff_winsGoingFirst.mp hgr'_out).right
      · have h_left_hr : WinsGoingFirst .left hr := by
          simpa [Player.neg_right] using
            (not_winsGoingFirst_iff.mp hh_out.right).right hr hhr
        have hhr_pfde := PFreeDeadEnding_of_mem_moves hh hhr
        cases hhr_out : MisereOutcome hr with
        | L => exact (misereOutcome_L_iff_winsGoingFirst.mp (misereOutcome_of_add_LL.aux hg hhr_pfde hgL hhr_out)).left
        | N => exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp
                 (miserePlayerOutcome_of_add_LN.aux hg hhr_pfde hgL hhr_out)
        | P => exact absurd hhr_out (misereOutcome_ne_P_of_pfree hhr_pfde)
        | R => exact absurd h_left_hr (misereOutcome_R_iff_winsGoingFirst.mp hhr_out).right
termination_by Form.birthday g + Form.birthday h
decreasing_by all_goals gameform_birthday

private theorem miserePlayerOutcome_of_add_LN.aux {g h : GameForm}
    (hg : PFreeDeadEnding g) (hh : PFreeDeadEnding h)
    (hgL : MisereOutcome g = .L) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .left = .left := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst]
  by_cases h_zero : h = 0
  · subst h
    simpa [add_zero] using (misereOutcome_L_iff_winsGoingFirst.mp hgL).left
  · have h_not_left_end : ¬IsEnd .left h :=
      fun h_left_end => h_zero (eq_zero_of_misereOutcome hh hhN h_left_end)
    rcases (winsGoingFirst_iff h .left).mp (misereOutcome_N_iff_winsGoingFirst.mp hhN).left with
        h_left_end | ⟨hl, hhl, hhl_not_right⟩
    · exact absurd (isEndLike_iff_isEnd.mp h_left_end) h_not_left_end
    · have hhl_pfde := PFreeDeadEnding_of_mem_moves hh hhl
      refine winsGoingFirst_of_moves ⟨g + hl, add_left_mem_moves_add hhl g, ?_⟩
      refine (misereOutcome_L_iff_winsGoingFirst.mp ?_).right
      apply misereOutcome_of_add_LL.aux hg hhl_pfde hgL
      exact misereOutcome_of_isPFree_not_winsGoingFirst hhl_pfde.p_free hhl_not_right
termination_by Form.birthday g + Form.birthday h
decreasing_by gameform_birthday

end

private theorem misereOutcome_of_add_RR.aux {g h : GameForm}
    (hg : PFreeDeadEnding g) (hh : PFreeDeadEnding h)
    (hgR : MisereOutcome g = .R) (hhR : MisereOutcome h = .R)
    : MisereOutcome (g + h) = .R := by
  rw [<-misereOutcome_neg_L_iff_misereOutcome]
  simpa [neg_add_rev, add_comm]
    using misereOutcome_of_add_LL.aux
            (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
            ((misereOutcome_neg_L_iff_misereOutcome).mpr hgR) ((misereOutcome_neg_L_iff_misereOutcome).mpr hhR)

private theorem miserePlayerOutcome_of_add_RN.aux {g h : GameForm}
    (hg : PFreeDeadEnding g) (hh : PFreeDeadEnding h)
    (hgR : MisereOutcome g = .R) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .right = .right := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst, <-Player.neg_left, <-winsGoingFirst_neg_iff]
  simpa [neg_add_rev, add_comm]
    using miserePlayerOutcome_eq_iff_winsGoingFirst.mp
          (miserePlayerOutcome_of_add_LN.aux
            (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
            ((misereOutcome_neg_L_iff_misereOutcome).2 hgR) (misereOutcome_neg_N_iff_misereOutcome.mpr hhN))


instance : OutcomeStable PFreeDeadEnding where
  misereOutcome_of_add_LL := misereOutcome_of_add_LL.aux
  misereOutcome_of_add_RR := misereOutcome_of_add_RR.aux
  miserePlayerOutcome_of_add_LN := miserePlayerOutcome_of_add_LN.aux
  miserePlayerOutcome_of_add_RN := miserePlayerOutcome_of_add_RN.aux

namespace PFreeDeadEnding

theorem misereGE_of_int_le (a b : ℤ) (h1 : a ≥ b) : b ≥m PFreeDeadEnding a :=
  OutcomeStable.misereGE_of_int_le PFreeDeadEnding b a h1

theorem misereGE_of_nat_le (a b : ℕ) (h1 : a ≥ b) : b ≥m PFreeDeadEnding a :=
  OutcomeStable.misereGE_of_nat_le PFreeDeadEnding b a h1

theorem a_one_MisereOutcome {a : ℤ} (h0 : 0 ≤ a) : MisereOutcome (!{{(a : GameForm)} | {1}}) = .R := by
  rw [misereOutcome_R_iff_winsGoingFirst]
  apply And.intro
  · refine winsGoingFirst_of_moves ⟨1, ?_⟩
    simp only [moves_ofSets, Set.mem_singleton_iff, Player.le_left, Player.neg_right, Player.le_left_eq, true_and]
    rw [not_winsGoingFirst_iff]
    apply And.intro (by simp)
    simp
  · rw [not_winsGoingFirst_iff]
    simp [isEnd_def, h0]

theorem a_one_pfreeDeadEnding {a : ℤ} (h0 : 0 ≤ a) : PFreeDeadEnding (!{{(a : GameForm)} | {1}}) where
  p_free := by
    unfold IsPFree
    apply And.intro
    · simp [a_one_MisereOutcome, h0]
    · intro p; cases p <;> simp
  dead_ending := by
    unfold IsDeadEnding
    apply And.intro <;> intro p <;> cases p
    · simp [isEnd_def]
    · simp [isEnd_def]
    · simp
    · simp

instance : Hereditary PFreeDeadEnding where
  has_option h1 h2 :=
    { p_free := isPFree_of_isOption h1.p_free h2
    , dead_ending := isDeadEnding_of_isOption h1.dead_ending h2
    }

theorem reduction_a_one_int {a : ℤ} (h0 : 0 ≤ a)
    : (!{{(a : GameForm)} | {1}}) =m PFreeDeadEnding ((a + 1) : ℤ) := by
  have h0' : 0 ≤ a + 1 := Int.le_add_one h0
  have h0'' : 0 < a + 1 := Int.le_iff_lt_add_one.mp h0
  refine MisereEq.of_antisymm ?_ ?_
  · apply Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding
    · simpa [Maintenance, h0'] using misereGE_of_int_le (a + 1) 0 h0'
    · simp only [Maintenance, moves_ofSets, Set.mem_singleton_iff, exists_eq_left]
      intro hl h_hl
      apply Or.inl
      have h_hl := eq_sub_one_of_mem_leftMoves_intCast h_hl
      rw [Int.add_sub_cancel a 1] at h_hl
      simp [h_hl]
    · simp [Proviso, isEnd_def]
    · simp [Proviso, isEnd_def, h0]
  · apply Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding
    · simp [Maintenance, h0']
    · simp [Maintenance, h0'']
    · simp [Proviso, Strong]
      intro _ x h2 h3
      have h4 : WinsGoingFirst .right x := winsGoingFirst_of_isEnd h3
      have h6 : MisereOutcome x ≤ .N := misereOutcome_le_N_of_winsGoingFirst_right h4
      apply Or.elim (Outcome.le_N_eq_N_or_R h6) <;> intro h7
      · rw [<-miserePlayerOutcome_eq_iff_winsGoingFirst]
        exact OutcomeStable.miserePlayerOutcome_of_add_RN (a_one_pfreeDeadEnding h0) h2 (a_one_MisereOutcome h0) h7
      · apply winsGoingFirst_right_of_misereOutcome_R
        exact OutcomeStable.misereOutcome_of_add_RR (a_one_pfreeDeadEnding h0) h2 (a_one_MisereOutcome h0) h7
    · simp [Proviso, isEnd_def]

private theorem reduction_ab_int.auxL {a b : ℤ} (h0 : 0 ≤ a) (h2 : 1 ≤ b) (h3 : b ≤ a + 2)
    : (!{{(a : GameForm)} | {(b : GameForm)}}) ≥m PFreeDeadEnding (!{{(a : GameForm)} | {(1 : GameForm)}}) := by
  apply Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding
  · simp only [Maintenance, moves_ofSets, Set.mem_singleton_iff, exists_eq_left, forall_eq]
    refine Or.inr ⟨((b - 1) : ℤ), leftMoves_intCast_zero_lt h2, ?_⟩
    exact misereGE_rw_right (reduction_a_one_int h0) (misereGE_of_int_le (a + 1) (b - 1) (by omega))
  · simp [Maintenance]
  · simp [Proviso, isEnd_def]
  · simp [Proviso, isEnd_def]

private theorem reduction_ab_int.auxR (a : ℤ) {b : ℤ} (h0 : 1 ≤ b)
    : (!{{(a : GameForm)} | {(1 : GameForm)}}) ≥m PFreeDeadEnding (!{{(a : GameForm)} | {(b : GameForm)}}) := by
  apply Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding
  · simp only [Maintenance, moves_ofSets, Set.mem_singleton_iff, exists_eq_left, forall_eq]
    apply Or.inl
    rw [<-Form.intCast_one]
    exact misereGE_of_int_le b (1 : ℕ) h0
  · simp [Maintenance]
  · simp [Proviso, isEnd_def]
  · simp [Proviso, isEnd_def]

theorem reduction_ab_int (a b : ℤ) (h0 : 0 ≤ a) (h1 : 1 ≤ b) (h2 : b ≤ a + 2)
    : (!{{(a : GameForm)} | {(b : GameForm)}}) =m PFreeDeadEnding ((a + 1) : ℤ) := by
  refine MisereEQ.trans ?_ (reduction_a_one_int h0)
  apply MisereEq.of_antisymm (reduction_ab_int.auxL h0 h1 h2) (reduction_ab_int.auxR a h1)

lemma strong_left_of_misereOutcome_L {A : GameForm → Prop} [PFree A] [OutcomeStable A] {g : GameForm}
    (h1 : A g) (h2 : MisereOutcome g = .L) : Strong A g .left := by
  intro x hx h3
  apply Or.elim (misereOutcome_of_isEnd_left hx (isEndLike_iff_isEnd.mp h3)) <;> intro h5
  · apply Or.elim (OutcomeStable.misereOutcome_of_add_LN h1 hx h2 h5) <;> intro h6
    · rw [<-miserePlayerOutcome_eq_iff_winsGoingFirst]
      exact (misereOutcome_N_iff_miserePlayerOutcome.mp h6).left
    · exact minsGoingFirst_left_of_misereOutcome_L h6
  · exact minsGoingFirst_left_of_misereOutcome_L (OutcomeStable.misereOutcome_of_add_LL h1 hx h2 h5)

lemma strong_right_of_misereOutcome_R {A : GameForm → Prop} [PFree A] [OutcomeStable A] {g : GameForm}
    (h1 : A g) (h2 : MisereOutcome g = .R) : Strong A g .right := by
  intro x hx h3
  apply Or.elim (misereOutcome_of_isEnd_right hx (isEndLike_iff_isEnd.mp h3)) <;> intro h5
  · apply Or.elim (OutcomeStable.misereOutcome_of_add_RN h1 hx h2 h5) <;> intro h6
    · rw [<-miserePlayerOutcome_eq_iff_winsGoingFirst]
      exact (misereOutcome_N_iff_miserePlayerOutcome.mp h6).right
    · exact winsGoingFirst_right_of_misereOutcome_R h6
  · exact winsGoingFirst_right_of_misereOutcome_R (OutcomeStable.misereOutcome_of_add_RR h1 hx h2 h5)

theorem proviso_pfreeDeadEnding_iff_proviso_deadEnding {g h : GameForm} {p : Player}
    : Proviso PFreeDeadEnding g h p ↔ Proviso IsDeadEnding g h p := by
  apply Iff.intro <;> intro h1
  · intro h2 x h3 h4
    have h5 : PFreeDeadEnding x :=
      { p_free := isPFree_of_isDeadEnd (isDeadEnd_of_isDeadEnding h3 (isEndLike_iff_isEnd.mp h4))
      , dead_ending := h3
      }
    exact h1 h2 x h5 h4
  · intro h2 x h3 h4
    exact h1 h2 x h3.dead_ending h4

private theorem reduction_ab_between_int_left.aux {a b : ℤ} (h0 : 0 ≤ a) (h1 : a + 2 ≤ b)
    : !{{(a : GameForm)}|{(b : GameForm)}} ≥m PFreeDeadEnding !{{((b - 2 : ℤ) : GameForm)}|{1}} := by
  apply Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding
  · simp only [Maintenance, moves_ofSets, Set.mem_singleton_iff, exists_eq_left, forall_eq]
    refine Or.inr ⟨(b - 1 : ℤ), leftMoves_intCast_zero_lt (by omega), ?_⟩
    have h2 := reduction_ab_int (b - 2) 1 (by omega) Int.le_rfl (by omega)
    rw [Form.intCast_ofNat, Nat.cast_one] at h2
    apply misereGE_rw_right h2
    have h3 : b - 2 + 1 = b - 1 := by omega
    rw [h3]
    exact MisereGE.refl _
  · simp only [Maintenance, moves_ofSets, Set.mem_singleton_iff, exists_eq_left, forall_eq]
    exact Or.inl (misereGE_of_int_le (b - 2) a (by omega))
  · simp [Proviso, isEnd_def]
  · simp [Proviso, isEnd_def]

theorem reduction_ab_between_int_left {a b : ℤ} (h0 : 0 ≤ a) (h1 : a + 2 ≤ b)
    : !{{(a : GameForm)}|{(b : GameForm)}} ≥m PFreeDeadEnding ((b - 1 : ℤ) : GameForm) := by
  refine misereGE_rw_right (MisereEQ.symm ?_) (reduction_ab_between_int_left.aux h0 h1)
  have h2 := reduction_ab_int (b - 2) 1 (by omega) Int.le_rfl (by omega)
  have h4 : b - 2 + 1 = b - 1 := by omega
  rwa [Form.intCast_ofNat, Nat.cast_one, h4] at h2

theorem reduction_ab_between_int_right {a b : ℤ} (h0 : 0 ≤ a) (h1 : 1 ≤ b)
    : ((a + 1 : ℤ) : GameForm) ≥m PFreeDeadEnding !{{(a : GameForm)}|{(b : GameForm)}} := by
  refine misereGE_rw_left ?_ (reduction_ab_int.auxR a h1)
  have h2 := reduction_ab_int a 1 h0 Int.le_rfl (by omega)
  norm_cast at h2

private theorem reduction_a_eq_neg_ba_c.aux {a b : ℤ} (h1 : 0 ≤ a) (h2 : 1 ≤ b)
    : !{{-(b : GameForm)} | {((a + 1 : ℤ) : GameForm)}} ≥m PFreeDeadEnding (a : GameForm) := by
  apply Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding
  · simp [Maintenance]
    apply Or.inr
    use a
    simp [leftMoves_intCast_zero_le_succ h1]
  · simp only [Maintenance, moves_ofSets, Player.cases, Set.mem_singleton_iff, exists_eq_left]
    intro x h5
    apply Or.inl
    obtain h_lt | h_eq := lt_or_eq_of_le h1
    · simp only [leftMoves_intCast h_lt, Set.mem_singleton_iff] at h5
      rw [h5, <-Form.intCast_neg]
      exact misereGE_of_int_le _ _ (by omega)
    · simp [h_eq] at h5
  · simp [Proviso, isEnd_def]
  · simp only [Proviso, isEndLike_iff_isEnd, isEnd_def]
    intro h5
    rw [leftMoves_intCast_le_zero_of_empty h1 h5]
    intro x h6 h7
    apply winsGoingFirst_of_moves
    use (-b : ℤ) + x, add_right_mem_moves_add (by simp) x
    rw [not_winsGoingFirst_iff]
    constructor
    · simp only [Player.neg_left, IsEndLike.add_iff, isEndLike_iff_isEnd, not_and]
      intro h8
      absurd h8
      simp [isEnd_def, leftMoves_intCast_le_one_ne_empty h2]
    · intro g' h8
      simp at h8
      apply Or.elim h8 <;> intro ⟨y, h9, h10⟩ <;> rw[<-h10]
      · apply winsGoingFirst_of_isEndLike
        simp only [leftMoves_intCast_le_one_eq h2, Set.mem_singleton_iff] at h9
        rw [neg_neg, IsEndLike.add_iff]
        refine And.intro ?_ h7
        simp only [h9, isEndLike_iff_isEnd, isEnd_def, moves_neg, Player.neg_left, Set.neg_eq_empty]
        exact rightMoves_intCast (Int.sub_nonneg_of_le h2)
      · apply winsGoingFirst_add_of_isEnd
        · simp only [isEnd_def, moves_neg, Set.neg_eq_empty]
          exact rightMoves_intCast (Int.le_of_lt h2)
        · apply isEnd_of_isDeadEnd
          refine IsDeadEnd.hereditary_def ?_ y h9
          exact isDeadEnd_of_isDeadEnding h6.dead_ending (isEndLike_iff_isEnd.mp h7)

theorem reduction_a_eq_neg_ba_c {a b c : ℤ} (h1 : 1 ≤ a) (h2 : 1 ≤ b) (h3 : 1 ≤ c) (h4 : c ≤ a + 1)
    : !{{!{{(((-b) : ℤ) : GameForm)}|{(a : GameForm)}}}|{(c : GameForm)}} =m PFreeDeadEnding (a : GameForm)  := by
  obtain ⟨a', h5⟩ := Int.le.dest h1
  norm_cast at h5
  rw [add_comm] at h5
  rw [<-h5]; norm_cast
  have h6 := reduction_ab_int a' 1 (Int.natCast_nonneg a') Int.le_rfl (by omega)
  rw [Form.intCast_nat] at h6
  refine MisereEQ.trans ?_ h6
  refine MisereEq.of_antisymm ?_ ?_
  · apply Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding
    · simp only [Maintenance, moves_ofSets, Player.cases, Set.mem_singleton_iff,
                 exists_eq_left, forall_eq]
      apply Or.inr
      use (c - 1 : ℤ), leftMoves_intCast_zero_lt h3
      apply misereGE_rw_right h6
      exact misereGE_of_int_le _ _ (by omega)
    · simp only [Maintenance, Form.intCast_ofNat, Nat.cast_one, moves_ofSets,
                 Player.cases, Set.mem_singleton_iff, Form.intCast_neg, Nat.cast_add, exists_eq_left,
                 forall_eq, rightMoves_natCast, Set.mem_empty_iff_false, false_and,
                 exists_const, or_false]
      have h3 := reduction_a_eq_neg_ba_c.aux (Int.natCast_nonneg a') h2
      norm_cast at h3
      norm_cast
    · simp [Proviso, isEnd_def]
    · simp [Proviso, isEnd_def]
  · apply Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding
    · simp only [Maintenance, moves_ofSets, Player.cases, Set.mem_singleton_iff, Form.intCast_neg,
                 exists_eq_left, forall_eq]
      apply Or.inl
      exact misereGE_of_int_le _ _ h3
    · simp only [Maintenance, Form.intCast_neg, Nat.cast_one,
                 moves_ofSets, Player.cases, Set.mem_singleton_iff, Form.intCast_ofNat, exists_eq_left,
                 forall_eq]
      apply Or.inr
      norm_cast at h6
      apply misereGE_rw_left (MisereEQ.symm h6)
      exact MisereGE.refl ((a' + 1) : GameForm)
    · simp [Proviso, isEnd_def]
    · simp [Proviso, isEnd_def]
