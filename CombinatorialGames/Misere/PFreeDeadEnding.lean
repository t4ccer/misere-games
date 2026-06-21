/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.DeadEnding

public section

universe u

open Form
open Form.Misere.Outcome
open GameForm
open PFree

private theorem misereOutcome_of_isPFree_not_winsGoingFirst {g : GameForm}
    (h_pfree : IsPFree g) (h_not_right : ¬WinsGoingFirst .right g) : MisereOutcome g = .L := by
  rw [misereOutcome_L_iff_winsGoingFirst]
  refine ⟨?_, h_not_right⟩
  by_contra h_not_left
  exact misereOutcome_ne_P_of_pfree h_pfree (misereOutcome_P_iff_winsGoingFirst.mpr ⟨h_not_right, h_not_left⟩)

private theorem eq_zero_of_misereOutcome {g : GameForm} (hg : IsDeadEnding g)
    (hN : MisereOutcome g = .N) (h_left_end : IsEnd .left g) : g = 0 := by
  by_contra h_ne_zero
  have h_left_dead := isDeadEnd_of_isDeadEnding hg h_left_end
  exact absurd (DeadEnding.isDeadEnd_left_misereOutcome_L g h_ne_zero h_left_dead) (by simp [hN])

mutual

private theorem misereOutcome_of_add_LL.aux {g h : GameForm}
    (hg : (PFreeSubset IsDeadEnding) g) (hh : (PFreeSubset IsDeadEnding) h)
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
      · have hhl_pfde := Hereditary.of_mem_moves hh hhl
        have hhlL := misereOutcome_of_isPFree_not_winsGoingFirst hhl_pfde.isPFree hhl_not_right
        have hsumL := misereOutcome_of_add_LL.aux hg hhl_pfde hgL hhlL
        exact winsGoingFirst_of_moves
          ⟨g + hl, add_left_mem_moves_add hhl g, (misereOutcome_L_iff_winsGoingFirst.mp hsumL).right⟩
    · have hgl_pfde := Hereditary.of_mem_moves hg hgl
      have hglL := misereOutcome_of_isPFree_not_winsGoingFirst hgl_pfde.isPFree hgl_not_right
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
        have hgr_pfde := Hereditary.of_mem_moves hg hgr'
        cases hgr'_out : MisereOutcome gr' with
        | L => exact (misereOutcome_L_iff_winsGoingFirst.mp (misereOutcome_of_add_LL.aux hgr_pfde hh hgr'_out hhL)).left
        | N => exact add_comm h gr' ▸ miserePlayerOutcome_eq_iff_winsGoingFirst.mp
                 (miserePlayerOutcome_of_add_LN.aux hh hgr_pfde hhL hgr'_out)
        | P => exact absurd hgr'_out (misereOutcome_ne_P_of_pfree hgr_pfde)
        | R => exact absurd h_left_gr' (misereOutcome_R_iff_winsGoingFirst.mp hgr'_out).right
      · have h_left_hr : WinsGoingFirst .left hr := by
          simpa [Player.neg_right] using
            (not_winsGoingFirst_iff.mp hh_out.right).right hr hhr
        have hhr_pfde := Hereditary.of_mem_moves hh hhr
        cases hhr_out : MisereOutcome hr with
        | L => exact (misereOutcome_L_iff_winsGoingFirst.mp (misereOutcome_of_add_LL.aux hg hhr_pfde hgL hhr_out)).left
        | N => exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp
                 (miserePlayerOutcome_of_add_LN.aux hg hhr_pfde hgL hhr_out)
        | P => exact absurd hhr_out (misereOutcome_ne_P_of_pfree hhr_pfde)
        | R => exact absurd h_left_hr (misereOutcome_R_iff_winsGoingFirst.mp hhr_out).right
termination_by Form.birthday g + Form.birthday h
decreasing_by all_goals gameform_birthday

private theorem miserePlayerOutcome_of_add_LN.aux {g h : GameForm}
    (hg : (PFreeSubset IsDeadEnding) g) (hh : (PFreeSubset IsDeadEnding) h)
    (hgL : MisereOutcome g = .L) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .left = .left := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst]
  by_cases h_zero : h = 0
  · subst h
    simpa [add_zero] using (misereOutcome_L_iff_winsGoingFirst.mp hgL).left
  · have h_not_left_end : ¬IsEnd .left h :=
      fun h_left_end => h_zero (eq_zero_of_misereOutcome hh.mem hhN h_left_end)
    rcases (winsGoingFirst_iff h .left).mp (misereOutcome_N_iff_winsGoingFirst.mp hhN).left with
        h_left_end | ⟨hl, hhl, hhl_not_right⟩
    · exact absurd (isEndLike_iff_isEnd.mp h_left_end) h_not_left_end
    · have hhl_pfde := Hereditary.of_mem_moves hh hhl
      refine winsGoingFirst_of_moves ⟨g + hl, add_left_mem_moves_add hhl g, ?_⟩
      refine (misereOutcome_L_iff_winsGoingFirst.mp ?_).right
      apply misereOutcome_of_add_LL.aux hg hhl_pfde hgL
      exact misereOutcome_of_isPFree_not_winsGoingFirst hhl_pfde.isPFree hhl_not_right
termination_by Form.birthday g + Form.birthday h
decreasing_by gameform_birthday

end

private theorem misereOutcome_of_add_RR.aux {g h : GameForm}
    (hg : (PFreeSubset IsDeadEnding) g) (hh : (PFreeSubset IsDeadEnding) h)
    (hgR : MisereOutcome g = .R) (hhR : MisereOutcome h = .R)
    : MisereOutcome (g + h) = .R := by
  rw [<-misereOutcome_neg_L_iff_misereOutcome]
  simpa [neg_add_rev, add_comm]
    using misereOutcome_of_add_LL.aux
            (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
            ((misereOutcome_neg_L_iff_misereOutcome).mpr hgR) ((misereOutcome_neg_L_iff_misereOutcome).mpr hhR)

private theorem miserePlayerOutcome_of_add_RN.aux {g h : GameForm}
    (hg : (PFreeSubset IsDeadEnding) g) (hh : (PFreeSubset IsDeadEnding) h)
    (hgR : MisereOutcome g = .R) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .right = .right := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst, <-Player.neg_left, <-winsGoingFirst_neg_iff]
  simpa [neg_add_rev, add_comm]
    using miserePlayerOutcome_eq_iff_winsGoingFirst.mp
          (miserePlayerOutcome_of_add_LN.aux
            (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
            ((misereOutcome_neg_L_iff_misereOutcome).2 hgR) (misereOutcome_neg_N_iff_misereOutcome.mpr hhN))


instance : OutcomeStable (IsDeadEnding (G := GameForm)) where
  misereOutcome_of_add_LL := misereOutcome_of_add_LL.aux
  misereOutcome_of_add_RR := misereOutcome_of_add_RR.aux
  miserePlayerOutcome_of_add_LN := miserePlayerOutcome_of_add_LN.aux
  miserePlayerOutcome_of_add_RN := miserePlayerOutcome_of_add_RN.aux

abbrev PFreeDeadEnding (g : GameForm) : Prop := (PFreeSubset DeadEnding.ShortDeadEnding) g

def PFreeDeadEnding.isDeadEnding {g : GameForm} (h_g : PFreeDeadEnding g) : IsDeadEnding g :=
  h_g.mem.dead_ending

instance : DeadEnding PFreeDeadEnding where
  isDeadEnding h := h.isDeadEnding

def PFreeDeadEnding.isShort {g : GameForm} (h_g : PFreeDeadEnding g) : IsShort g :=
  h_g.mem.short

instance : OutcomeStable (DeadEnding.ShortDeadEnding (G := GameForm)) where
  misereOutcome_of_add_LL hg hh hgL hhL := misereOutcome_of_add_LL.aux
    (.mk hg.mem.dead_ending hg.isPFree) (.mk hh.mem.dead_ending hh.isPFree) hgL hhL
  misereOutcome_of_add_RR hg hh hgR hhR := misereOutcome_of_add_RR.aux
    (.mk hg.mem.dead_ending hg.isPFree) (.mk hh.mem.dead_ending hh.isPFree) hgR hhR
  miserePlayerOutcome_of_add_LN hg hh hgL hhN := miserePlayerOutcome_of_add_LN.aux
    (.mk hg.mem.dead_ending hg.isPFree) (.mk hh.mem.dead_ending hh.isPFree) hgL hhN
  miserePlayerOutcome_of_add_RN hg hh hgR hhN := miserePlayerOutcome_of_add_RN.aux
    (.mk hg.mem.dead_ending hg.isPFree) (.mk hh.mem.dead_ending hh.isPFree) hgR hhN

instance : ClosedUnderAddNat (DeadEnding.ShortDeadEnding (G := GameForm)) where
  has_add h_g n :=
    { dead_ending := DeadEnding.IsDeadEnding.add h_g.dead_ending (DeadEnding.isDeadEnding_natCast n)
    , short := Short.add (h_g.short) (Short.natCast n)
    }

instance : ClosedUnderAdd (DeadEnding.ShortDeadEnding (G := GameForm)) where
  has_add _ _  h_g h_h :=
    { dead_ending := DeadEnding.IsDeadEnding.add h_g.dead_ending h_h.dead_ending
    , short := Short.add h_g.short h_h.short
    }

instance : ClosedUnderAdd PFreeDeadEnding where
  has_add g h h_g h_h := by
    apply PFreeSubset.mk
    · exact ClosedUnderAdd.has_add g h h_g.mem h_h.mem
    · exact IntegerInvertible.isPFree_of_propertyX h_g h_h h_g.isShort h_h.isShort

namespace PFreeDeadEnding

theorem misereGE_of_int_le (a b : ℤ) (h1 : a ≥ b) : b ≥m PFreeDeadEnding a :=
  OutcomeStable.misereGE_of_int_le _ b a h1

theorem misereGE_of_nat_le (a b : ℕ) (h1 : a ≥ b) : b ≥m PFreeDeadEnding a :=
  OutcomeStable.misereGE_of_nat_le _ b a h1

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

theorem a_one_pfreeDeadEnding {a : ℤ} (h0 : 0 ≤ a) : PFreeDeadEnding (!{{(a : GameForm)} | {1}}) := by
  apply PFreeSubset.mk
  · exact
    { dead_ending := by
        unfold IsDeadEnding
        apply And.intro <;> intro p <;> cases p
        · simp [isEnd_def]
        · simp [isEnd_def]
        · simp
        · simp
      short := by
        rw [short_def]
        intro p; cases p
        · simp
        · simp
    }
  · unfold IsPFree
    apply And.intro
    · simp [a_one_MisereOutcome, h0]
    · intro p; cases p <;> simp

theorem misereGE_of_maintenance_proviso
    {g h : GameForm} (hg : IsPFree g) (hh : IsPFree h)
    (h_m_r : Maintenance PFreeDeadEnding g h .right) (h_m_l : Maintenance PFreeDeadEnding g h .left)
    (h_p_r : IsEnd .right g → MisereOutcome h ≠ .L) (h_p_l : IsEnd .left h → MisereOutcome g ≠ .R)
    : g ≥m PFreeDeadEnding h := by
  refine Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding h_m_r h_m_l ?_ ?_
  · intro h_isEnd
    rw [GameForm.isEndLike_iff_isEnd] at h_isEnd
    rw [PFree.strong_right_iff_misereOutcome_L hh]
    exact h_p_r h_isEnd
  · intro h_isEnd
    rw [GameForm.isEndLike_iff_isEnd] at h_isEnd
    rw [PFree.strong_left_iff_misereOutcome_R hg]
    exact h_p_l h_isEnd

theorem reduction_a_one_int {a : ℤ} (h0 : 0 ≤ a)
    : (!{{(a : GameForm)} | {1}}) =m PFreeDeadEnding ((a + 1) : ℤ) := by
  have h0' : 0 ≤ a + 1 := Int.le_add_one h0
  have h0'' : 0 < a + 1 := Int.le_iff_lt_add_one.mp h0
  refine MisereEq.of_antisymm ?_ ?_
  · apply misereGE_of_maintenance_proviso (a_one_pfreeDeadEnding h0).isPFree (HasInt.has_int _)
    · simpa [Maintenance, h0'] using misereGE_of_int_le (a + 1) 0 h0'
    · simp only [Maintenance, moves_ofSets, Set.mem_singleton_iff, exists_eq_left]
      intro hl h_hl
      apply Or.inl
      have h_hl := eq_sub_one_of_mem_leftMoves_intCast h_hl
      rw [Int.add_sub_cancel a 1] at h_hl
      simp [h_hl]
    · simp [isEnd_def]
    · simp [isEnd_def, h0]
  · apply misereGE_of_maintenance_proviso (HasInt.has_int _) (a_one_pfreeDeadEnding h0).isPFree
    · simp [Maintenance, h0']
    · simp [Maintenance, h0'']
    · intro h1 h2
      rw [misereOutcome_L_iff_winsGoingFirst] at h2
      absurd h2.right
      apply winsGoingFirst_of_moves
      simp
    · simp [isEnd_def]

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
    (h1 : (PFreeSubset A) g) (h2 : MisereOutcome g = .L) : Strong (PFreeSubset A) g .left := by
  intro x hx h3
  apply Or.elim (misereOutcome_of_isEnd_left hx (isEndLike_iff_isEnd.mp h3)) <;> intro h5
  · apply Or.elim (OutcomeStable.misereOutcome_of_add_LN h1 hx h2 h5) <;> intro h6
    · rw [<-miserePlayerOutcome_eq_iff_winsGoingFirst]
      exact (misereOutcome_N_iff_miserePlayerOutcome.mp h6).left
    · exact minsGoingFirst_left_of_misereOutcome_L h6
  · exact minsGoingFirst_left_of_misereOutcome_L (OutcomeStable.misereOutcome_of_add_LL h1 hx h2 h5)

lemma strong_right_of_misereOutcome_R {A : GameForm → Prop} [PFree A] [OutcomeStable A] {g : GameForm}
    (h1 : (PFreeSubset A) g) (h2 : MisereOutcome g = .R) : Strong (PFreeSubset A) g .right := by
  intro x hx h3
  apply Or.elim (misereOutcome_of_isEnd_right hx (isEndLike_iff_isEnd.mp h3)) <;> intro h5
  · apply Or.elim (OutcomeStable.misereOutcome_of_add_RN h1 hx h2 h5) <;> intro h6
    · rw [<-miserePlayerOutcome_eq_iff_winsGoingFirst]
      exact (misereOutcome_N_iff_miserePlayerOutcome.mp h6).right
    · exact winsGoingFirst_right_of_misereOutcome_R h6
  · exact winsGoingFirst_right_of_misereOutcome_R (OutcomeStable.misereOutcome_of_add_RR h1 hx h2 h5)

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

private theorem reduction_a_eq_neg_ba_c.aux {a b : ℤ} (h1 : 0 ≤ a) (h2 : 0 < b)
    : !{{-(b : GameForm)} | {((a + 1 : ℤ) : GameForm)}} ≥m PFreeDeadEnding (a : GameForm) := by
  apply misereGE_of_maintenance_proviso ?_ (HasInt.has_int _)
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
  · simp [isEnd_def]
  · intro h5 h6
    have : a = 0 := by exact Eq.symm (Int.le_antisymm h1 (isEnd_left_intCast_iff.mp h5))
    subst this
    rw [misereOutcome_R_iff_winsGoingFirst] at h6
    absurd h6.right
    apply winsGoingFirst_of_moves
    use -b
    constructor
    · simp only [zero_add, Form.intCast_ofNat, Nat.cast_one, leftMoves_ofSets, Set.mem_singleton_iff]
    · rw [not_winsGoingFirst_iff]
      simp [h2]
      rw [<-Form.intCast_neg, winsGoingFirst_left_intCast_iff]
      omega
  · unfold IsPFree
    constructor
    · intro h3
      rw [misereOutcome_P_iff_winsGoingFirst] at h3
      absurd h3.right
      apply winsGoingFirst_of_moves
      simp [h2, <-Form.intCast_neg]
    · intro p gp h_gp
      cases p
      <;> simp only [leftMoves_ofSets, rightMoves_ofSets, Set.mem_singleton_iff] at h_gp
      <;> simp only [h_gp, isPFree_intCast, ClosedUnderNeg.neg_iff]

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

private theorem misereEQ_intCast_pred_of_options {g : GameForm.{u}} (n : ℤ) (hn : n ≤ 0)
    (h_isEnd : IsEnd .left g)
    (h_all_ge : ∀ gr ∈ moves .right g, gr ≥m PFreeDeadEnding ((n : ℤ) : GameForm))
    (h_exists_n : ∃ gr ∈ moves .right g, ((n : ℤ) : GameForm) ≥m PFreeDeadEnding gr) :
    g =m PFreeDeadEnding ((n - 1 : ℤ) : GameForm) := by
  have hRM : moves .right ((n - 1 : ℤ) : GameForm.{u}) = {((n : ℤ) : GameForm.{u})} := by
    have key : ((n - 1 : ℤ)) = -((1 - n : ℤ)) := by omega
    rw [key, Form.intCast_neg, moves_neg, Player.neg_right, leftMoves_intCast (by omega),
       show ((1 - n : ℤ) - 1) = -n by omega, Form.intCast_neg, Set.neg_singleton, neg_neg]
  have hL0 : moves .left ((n - 1 : ℤ) : GameForm.{u}) = ∅ := by
    have := isEnd_of_isDeadEnd (isDeadEnd_left_nonpos_intCast (G := GameForm.{u}) (n - 1) (by omega))
    rwa [isEnd_def] at this
  have hLg : moves .left g = ∅ := by rwa [isEnd_def] at h_isEnd
  have hEnd_h : IsEnd .left ((n - 1 : ℤ) : GameForm.{u}) :=
    isEnd_of_isDeadEnd (isDeadEnd_left_nonpos_intCast (G := GameForm.{u}) (n - 1) (by omega))
  have hge : g ≥m PFreeDeadEnding ((n - 1 : ℤ) : GameForm) := by
    apply Form.Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding
    · intro gr hgr
      exact Or.inl ⟨((n : ℤ) : GameForm), by rw [hRM]; rfl, h_all_ge gr hgr⟩
    · intro hl hhl; rw [hL0] at hhl; exact absurd hhl (Set.notMem_empty _)
    · intro hcontra
      obtain ⟨gr, hgr, _⟩ := h_exists_n
      rw [GameForm.isEndLike_iff_isEnd, isEnd_def] at hcontra
      rw [hcontra] at hgr; exact absurd hgr (Set.notMem_empty _)
    · exact fun _ => strong_of_isEnd h_isEnd
  have hle : ((n - 1 : ℤ) : GameForm) ≥m PFreeDeadEnding g := by
    apply Form.Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding
    · intro hr hhr
      rw [hRM, Set.mem_singleton_iff] at hhr
      obtain ⟨gr, hgr, hgex⟩ := h_exists_n
      exact Or.inl ⟨gr, hgr, by rw [hhr]; exact hgex⟩
    · intro gl hgl; rw [hLg] at hgl; exact absurd hgl (Set.notMem_empty _)
    · intro hcontra
      rw [GameForm.isEndLike_iff_isEnd, isEnd_def, hRM] at hcontra
      exact absurd hcontra (by simp)
    · exact fun _ => strong_of_isEnd hEnd_h
  exact MisereEq.of_antisymm hge hle

private theorem exists_intCast_of_options_misereEQ {g : GameForm.{u}}
    (h_isEnd_left : IsEnd .left g) (h_not_isEnd_right : ¬IsEnd .right g)
    (h_mem_right : ∀ gr ∈ moves .right g, ∃ n : ℕ, gr =m PFreeDeadEnding ((-(n : ℤ) : ℤ) : GameForm)) :
    ∃ n : ℕ, g =m PFreeDeadEnding ((-(n : ℤ) : ℤ) : GameForm) := by
  set S := {n : ℕ | ∃ gr ∈ moves Player.right g, gr =m PFreeDeadEnding ((-(n : ℤ) : ℤ) : GameForm)}
    with hS_def
  have h_S_nonempty : S.Nonempty := by
    have : (moves .right g).Nonempty := by
      rw [isEnd_def] at h_not_isEnd_right
      exact Set.nonempty_iff_empty_ne.mpr fun a ↦ h_not_isEnd_right (Eq.symm a)
    exact this.elim fun x hx => (h_mem_right x hx).elim fun a ha => ⟨a, x, hx, ha⟩
  set M := sInf S with hM_def
  obtain ⟨gr0, h_gr0_mem, h_gr0_eq⟩ :
      ∃ gr0 ∈ moves Player.right g, gr0 =m PFreeDeadEnding ((-(M : ℤ) : ℤ) : GameForm) :=
    Nat.sInf_mem h_S_nonempty
  have h_M_le : ∀ a ∈ S, M ≤ a := fun a ha => Nat.sInf_le ha
  have h_misereEQ : g =m PFreeDeadEnding ((-(M : ℤ) - 1 : ℤ) : GameForm) := by
    refine misereEQ_intCast_pred_of_options ((-(M : ℤ) : ℤ)) (by omega) h_isEnd_left ?_
      ⟨gr0, h_gr0_mem, misereGE_of_misereEQ h_gr0_eq.symm⟩
    intro gr h_gr_mem
    obtain ⟨a, ha⟩ := h_mem_right gr h_gr_mem
    have h_M_le_a : M ≤ a := h_M_le a ⟨gr, h_gr_mem, ha⟩
    exact misereGE_rw_left (MisereEQ.symm ha)
      (PFreeDeadEnding.misereGE_of_int_le (-M : ℤ) (-a : ℤ) (by omega))
  exact ⟨M + 1, by simpa [neg_add_eq_sub] using h_misereEQ⟩

private theorem isEnd_left_exists_intCast_misereEQ {g : GameForm}
    (h_g : PFreeDeadEnding g) (h_isEnd_left : IsEnd .left g) :
    ∃ n : ℕ, g =m PFreeDeadEnding ((-(n : ℤ) : ℤ) : GameForm) := by
  by_cases h_isEnd_right : IsEnd .right g
  · use 0
    have h_g_eq_zero : g = 0 := both_ends_eq_zero h_isEnd_left h_isEnd_right
    subst h_g_eq_zero
    intro x _
    simp
  · have h_isDeadEnd_g := isDeadEnd_of_isDeadEnding h_g.isDeadEnding h_isEnd_left
    have h_opt : ∀ gr ∈ moves .right g,
        ∃ n : ℕ, gr =m PFreeDeadEnding ((-(n : ℤ) : ℤ) : GameForm) := by
      intro gr h_gr
      have h_pf_deadEnding_gr := Hereditary.of_mem_moves h_g h_gr
      have h_isEnd_gr := isEnd_of_isDeadEnd (isDeadEnd_of_mem_moves h_isDeadEnd_g h_gr)
      exact isEnd_left_exists_intCast_misereEQ h_pf_deadEnding_gr h_isEnd_gr
    exact exists_intCast_of_options_misereEQ h_isEnd_left h_isEnd_right h_opt
termination_by g
decreasing_by form_wf

private theorem isEnd_right_exists_intCast_misereEQ {g : GameForm}
    (h_g : PFreeDeadEnding g) (h_isEnd : IsEnd .right g) :
    ∃ n : ℕ, g =m PFreeDeadEnding ((n : ℤ) : GameForm) := by
  obtain ⟨n, ha⟩ := isEnd_left_exists_intCast_misereEQ
      (ClosedUnderNeg.neg_of h_g) (IsEnd.neg_iff_neg.mpr h_isEnd)
  use n
  rwa [Form.intCast_neg n, misereEQ_neg_iff] at ha

/--
If $G \in \operatorname{pf}(\mathcal{E})$ is an end, then it is equivalent to
some integer.
-/
theorem isEnd_exists_intCast_misereEQ {p : Player} {g : GameForm} (h_g : PFreeDeadEnding g)
    (h_isEnd : IsEnd p g) :
    ∃ k : ℤ, g =m PFreeDeadEnding ((k : ℤ) : GameForm) := by
  cases p
  · obtain ⟨a, ha⟩ := isEnd_left_exists_intCast_misereEQ h_g h_isEnd
    exact ⟨-(a : ℤ), ha⟩
  · obtain ⟨a, ha⟩ := isEnd_right_exists_intCast_misereEQ h_g h_isEnd
    exact ⟨(a : ℤ), ha⟩

theorem pfreeDeadEnding_ofSets {L R : Set GameForm} [Small.{u} L] [Small.{u} R]
    (h_L_mem : ∀ gl ∈ L, PFreeDeadEnding gl) (h_R_mem : ∀ gr ∈ R, PFreeDeadEnding gr)
    (h_L_nonempty : L.Nonempty) (h_L_finite : L.Finite)
    (h_R_nonempty : R.Nonempty) (h_R_finite : R.Finite)
    (h_outcome_ne_P : MisereOutcome (!{L | R}) ≠ .P) :
    PFreeDeadEnding (!{L | R}) := by
  have h_moves : ∀ p x, x ∈ moves p (!{L | R}) → PFreeDeadEnding x := by
    intro p x h_x_mem
    cases p
    · rw [leftMoves_ofSets] at h_x_mem; exact h_L_mem x h_x_mem
    · rw [rightMoves_ofSets] at h_x_mem; exact h_R_mem x h_x_mem
  apply PFreeSubset.mk
  · refine ⟨?_, ?_⟩
    · refine Short.ofSets h_L_finite ?_ h_R_finite ?_
      · intro gl h_gl
        exact (h_L_mem gl h_gl).isShort
      · intro gr h_gr
        exact (h_R_mem gr h_gr).isShort
    · unfold IsDeadEnding
      refine ⟨?_, ?_⟩
      · intro p h_isEnd
        exfalso
        cases p
        · rw [isEnd_def, leftMoves_ofSets] at h_isEnd
          exact h_L_nonempty.ne_empty h_isEnd
        · rw [isEnd_def, rightMoves_ofSets] at h_isEnd
          exact h_R_nonempty.ne_empty h_isEnd
      · intro p gp hgp
        exact (h_moves p gp hgp).isDeadEnding
  · unfold IsPFree
    refine ⟨h_outcome_ne_P, ?_⟩
    intro p gp h_gp_mem
    exact (h_moves p gp h_gp_mem).isPFree

theorem rightSeparating_of_leftSeparating {g h : GameForm}
    (h_h : IsShort h) (h_left : AreLeftSeparating PFreeDeadEnding g h) :
    AreRightSeparating PFreeDeadEnding g h := by
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
  · apply pfreeDeadEnding_ofSets
    · intro a h_a_mem
      rw [h_L_def] at h_a_mem
      rcases h_a_mem with ⟨r, rfl⟩ | rfl
      · exact HasInt.has_neg_int (A := PFreeDeadEnding) _
      · exact HasInt.has_int (A := PFreeDeadEnding) (-1)
    · intro a h_a_mem
      rw [Set.mem_singleton_iff] at h_a_mem
      subst h_a_mem
      exact h_x_pf
    · exact ⟨_, h_conj_one_mem⟩
    · rw [h_L_def]
      have := Short.finite_moves' .right h_h
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
    · intro k hk
      rw [moves_add] at hk
      rw [Player.neg_right]
      rcases hk with ⟨h_r, h_r_mem, rfl⟩ | ⟨r, h_r_mem, rfl⟩
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

theorem rightSeparating_iff_leftSeparating {g h : GameForm} (h_g : IsShort g) (h_h : IsShort h) :
    AreRightSeparating PFreeDeadEnding g h ↔ AreLeftSeparating PFreeDeadEnding g h := by
  constructor
  · intro h_right
    have h1 := Separation.leftSeparating_neg_of_rightSeparating h_right
    have h2 := rightSeparating_of_leftSeparating
      (ClosedUnderNeg.neg_of h_g) h1
    simpa using Separation.leftSeparating_neg_of_rightSeparating h2
  · exact rightSeparating_of_leftSeparating h_h

instance : Separating IsShort PFreeDeadEnding where
  separating_pair_of_not_misereGE h_g h_h h_not_ge := by
    rcases not_misereGE_iff_separating.mp h_not_ge with h_left | h_right
    · rw [rightSeparating_iff_leftSeparating h_g h_h]
      exact ⟨h_left, h_left⟩
    · rw [<-rightSeparating_iff_leftSeparating h_g h_h]
      exact ⟨h_right, h_right⟩

-- TODO: Move
private theorem misereGE_zero_of_misereOutcome_L
    {A : GameForm → Prop} [OutcomeStable A]
    {g : GameForm} (h_g : (PFreeSubset A) g) (h_L : MisereOutcome g = .L) :
    g ≥m (PFreeSubset A) ((0 : ℤ) : GameForm) := by
  intro x hx
  rw [Form.intCast_zero, zero_add]
  cases hxo : MisereOutcome x with
  | R => exact Outcome.ge_R _
  | N =>
    exact IntegerInvertible.misereOutcome_add_ge_N_of_misereOutcome_L_left h_g hx h_L (Or.inl hxo)
  | L =>
    rw [OutcomeStable.misereOutcome_of_add_LL h_g hx h_L hxo]
  | P => exact absurd hxo (misereOutcome_ne_P_of_pfree hx)

-- TODO: Move
private theorem misereGE_intCast_of_misereOutcome_L
    {A : GameForm → Prop} [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    {g : GameForm} {n : ℤ}
    (h_g : (PFreeSubset A) g) (h_n : 0 ≤ n) (h_L : MisereOutcome g = .L) :
    g ≥m (PFreeSubset A) ((n : ℤ) : GameForm) :=
  MisereGE.trans (misereGE_zero_of_misereOutcome_L h_g h_L)
    (OutcomeStable.misereGE_of_int_le _ 0 n h_n)

-- TODO: Move
/--
If $\mathcal{A}$ is outcome-stable monoid closed under conjugation and
$G \in \operatorname{pf}(\mathcal{A})$ such that $\operatorname{o}(G) = \mathscr{R}$
then \operatorname{o}(G + \overline{1}) \ne \mathscr{L}$
-/
private theorem misereOutcome_add_neg_one_ne_L_of_R
    {A : GameForm → Prop}
    [OutcomeStable A] [ClosedUnderAddNat A] [ClosedUnderAdd A] [HasInt A] [ClosedUnderNeg A]
    {g : GameForm}
    (h_g : (PFreeSubset A) g) (h_g_isShort : IsShort g) (h_out_R : MisereOutcome g = .R) :
    MisereOutcome (g + ((-1 : ℤ) : GameForm)) ≠ .L := by
  intro hL
  have h_out_N : MisereOutcome (g + (-((NTippingPoint h_g_isShort : ℕ) : GameForm))) = .N := by
    rcases NTippingPoint_spec h_g_isShort with hpos | hneg
    · exfalso
      have hle := OutcomeStable.misereOutcome_add_natCast_le h_g.mem h_g.isPFree (NTippingPoint h_g_isShort)
      rw [h_out_R, Outcome.le_R_iff, hpos] at hle
      exact absurd hle (by decide)
    · exact hneg
  -- But if `o(g + (-1)) = .L`, antitonicity makes that same shift `.L`.
  have h_ntip_pos : 1 ≤ NTippingPoint h_g_isShort := by
    rcases Nat.eq_zero_or_pos (NTippingPoint h_g_isShort) with h0 | h
    · exfalso
      rw [h0] at h_out_N
      simp only [Nat.cast_zero, neg_zero, add_zero] at h_out_N
      rw [h_out_R] at h_out_N
      exact absurd h_out_N (by decide)
    · exact h
  have hle : (-((NTippingPoint h_g_isShort : ℕ) : ℤ)) ≤ (-1 : ℤ) := by
    have : (1 : ℤ) ≤ ((NTippingPoint h_g_isShort : ℕ) : ℤ) := by exact_mod_cast h_ntip_pos
    omega
  have hmono := OutcomeStable.misereOutcome_add_int_antitone h_g hle
  rw [hL] at hmono
  have heq : (((-((NTippingPoint h_g_isShort : ℕ) : ℤ)) : ℤ) : GameForm)
      = -((NTippingPoint h_g_isShort : ℕ) : GameForm) := by
    rw [Form.intCast_neg]; rfl
  rw [heq] at hmono
  have hLnt : MisereOutcome (g + (-((NTippingPoint h_g_isShort : ℕ) : GameForm))) = .L :=
    le_antisymm (Outcome.L_ge _) hmono
  rw [hLnt] at h_out_N
  exact absurd h_out_N (by decide)

-- TODO: Move
private theorem misereOutcome_R_of_not_leftMoves_misereGE
    {A : GameForm → Prop}
    [Hereditary A] [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    {g : GameForm} {n : ℤ}
    (h_g : (PFreeSubset A) g) (h_not_left_end : ¬ IsEnd .left g) (h_n : 0 ≤ n)
    (h : ∀ gl ∈ moves .left g, ¬ (gl ≥m (PFreeSubset A) ((n : ℤ) : GameForm))) :
    MisereOutcome g = .R := by
  by_contra hgR
  -- `g` is P-free, so its outcome is not `.P`; it is not `.R` by assumption,
  -- so Left wins going first.
  have hwf : WinsGoingFirst .left g := by
    cases hgo : MisereOutcome g with
    | P => exact absurd hgo (misereOutcome_ne_P_of_pfree h_g)
    | R => exact absurd hgo hgR
    | L => exact (misereOutcome_L_iff_winsGoingFirst.mp hgo).left
    | N => exact (misereOutcome_N_iff_winsGoingFirst.mp hgo).left
  -- A winning Left first move is a Left option `gl` with `¬ WinsGoingFirst .right gl`.
  rw [winsGoingFirst_iff] at hwf
  rcases hwf with hend | ⟨gl, hgl, hglnr⟩
  · exact h_not_left_end (GameForm.isEndLike_iff_isEnd.mp hend)
  · -- Such a `gl` is a P-free Left win, hence dominates `n`, contradicting `h`.
    have h_gl_pf := Hereditary.of_mem_moves h_g hgl
    have h_gl_L : MisereOutcome gl = .L := by
      cases hglo : MisereOutcome gl with
      | L => rfl
      | P => exact absurd hglo (misereOutcome_ne_P_of_pfree h_gl_pf)
      | N => exact absurd (misereOutcome_N_iff_winsGoingFirst.mp hglo).2 hglnr
      | R => exact absurd (misereOutcome_R_iff_winsGoingFirst.mp hglo).1 hglnr
    exact h gl hgl (misereGE_intCast_of_misereOutcome_L h_gl_pf h_n h_gl_L)

private theorem winsGoingFirst_right_sub_one_of_not_leftMoves_misereGE
    {A : GameForm → Prop}
    [Hereditary A] [OutcomeStable A] [HasInt A]
    [ClosedUnderAddNat A] [ClosedUnderAdd A] [ClosedUnderNeg A]
    {g : GameForm} {n : ℤ}
    (h_g : (PFreeSubset A) g) (h_isShort : IsShort g) (h_not_left_end : ¬ IsEnd .left g)
    (h_n : 0 ≤ n) (h : ∀ gl ∈ moves .left g, ¬ (gl ≥m (PFreeSubset A) ((n : ℤ) : GameForm))) :
    WinsGoingFirst .right (g + ((-1 : ℤ) : GameForm)) := by
  have hgR := misereOutcome_R_of_not_leftMoves_misereGE h_g h_not_left_end h_n h
  cases ho : MisereOutcome (g + ((-1 : ℤ) : GameForm)) with
  | L => exact absurd ho (misereOutcome_add_neg_one_ne_L_of_R h_g h_isShort hgR)
  | P => exact absurd ho (OutcomeStable.misereOutcome_add_int_ne_P h_g (-1))
  | N => exact (misereOutcome_N_iff_winsGoingFirst.mp ho).right
  | R => exact (misereOutcome_R_iff_winsGoingFirst.mp ho).left

-- TODO: This could be generalized once we have [Short A]
private theorem downlinked_intCast_of_not_leftMoves_misereGE {g : GameForm} {n : ℤ}
    (h_g : PFreeDeadEnding g) (h_not_left_end : ¬ IsEnd .left g) (h_n : 0 ≤ n)
    (h : ∀ gl ∈ moves .left g, ¬ (gl ≥m PFreeDeadEnding ((n : ℤ) : GameForm))) :
    Form.Downlinked PFreeDeadEnding g ((n : ℤ) : GameForm) := by

  -- For each Left option `gl` of `g`, the pair `(gl, n)` is left-separating.
  have hsep : ∀ gl, gl ∈ moves .left g → ∃ y : GameForm, PFreeDeadEnding y ∧
      ¬ WinsGoingFirst .left (gl + y) ∧ WinsGoingFirst .left (((n : ℤ) : GameForm) + y) := by
    intro gl hgl
    exact (Separating.separating_pair_of_not_misereGE
      (Short.of_mem_moves h_g.isShort hgl) (Short.intCast n) (h _ hgl)).1
  choose x hx_pf hx_g hx_n using hsep
  set R : Set GameForm := Set.range (fun gl : (moves .left g) => x gl.1 gl.2) with hR_def
  set t : GameForm := !{{((-1 : ℤ) : GameForm)} | R} with ht_def
  have htL : moves .left t = {((-1 : ℤ) : GameForm)} := by rw [ht_def, leftMoves_ofSets]
  have htR : moves .right t = R := by rw [ht_def, rightMoves_ofSets]
  -- Membership of the witness.
  have ht_pf : PFreeDeadEnding t := by
    rw [ht_def]
    refine pfreeDeadEnding_ofSets ?_ ?_
      (Set.singleton_nonempty _) (Set.finite_singleton _) ?_ ?_ ?_
    · intro a ha; rw [Set.mem_singleton_iff] at ha; subst ha; exact HasInt.has_int (-1 : ℤ)
    · rintro a ⟨⟨gl, hgl⟩, rfl⟩; exact hx_pf gl hgl
    · obtain ⟨gl, hgl⟩ := not_isEnd_exists_move h_not_left_end
      exact ⟨x gl hgl, ⟨gl, hgl⟩, rfl⟩
    · have : Finite (moves .left g) := Short.finite_moves' .left h_g.isShort
      exact Set.toFinite _
    · -- `o(t) ≠ .P`: Left wins going first by moving `t → -1` (an `.L` position).
      intro hP
      refine (misereOutcome_P_iff_winsGoingFirst.mp hP).2
        (winsGoingFirst_of_moves ⟨((-1 : ℤ) : GameForm), ?_, ?_⟩)
      · rw [leftMoves_ofSets]; exact Set.mem_singleton _
      · refine (misereOutcome_L_iff_winsGoingFirst.mp ?_).right
        rw [misereOutcome_L_intCast_iff]
        exact neg_one_lt_zero
  use t, ht_pf
  constructor
  · have hpf : IsPFree (g + t) := (ClosedUnderAdd.has_add g t h_g ht_pf).isPFree
    rw [not_winsGoingFirst_iff]
    refine ⟨?_, ?_⟩
    · rw [GameForm.isEndLike_iff_isEnd]
      exact fun hend => h_not_left_end (IsEnd.add_iff.mp hend).1
    · intro p hp
      rw [moves_add] at hp
      rcases hp with ⟨gl, hgl, rfl⟩ | ⟨tl, htl, rfl⟩
      · -- `p = gl + t`: Right answers `t → x gl`, reaching the Left loss `gl + x gl`.
        refine winsGoingFirst_of_moves ⟨gl + x gl hgl, ?_, hx_g gl hgl⟩
        refine add_left_mem_moves_add (?_ : x gl hgl ∈ moves Player.right t) gl
        rw [htR]
        exact ⟨⟨gl, hgl⟩, rfl⟩
      · -- `p = g + (-1)`, where Right wins going first.
        rw [htL, Set.mem_singleton_iff] at htl; subst htl
        exact winsGoingFirst_right_sub_one_of_not_leftMoves_misereGE h_g h_g.isShort h_not_left_end h_n h
  · have hpf : IsPFree (((n : ℤ) : GameForm) + t) :=
      (ClosedUnderAdd.has_add _ t (HasInt.has_int n) ht_pf).isPFree
    -- refine misereOutcome_of_isPFree_not_winsGoingFirst hpf ?_
    rw [not_winsGoingFirst_iff]
    refine ⟨?_, ?_⟩
    · -- not right-end-like: `t` has Right options.
      rw [GameForm.isEndLike_iff_isEnd]
      intro hend
      have htend : IsEnd .right t := (IsEnd.add_iff.mp hend).right
      rw [isEnd_def, htR] at htend
      simp only [hR_def, Set.range_eq_empty_iff, Set.isEmpty_coe_sort, ←isEnd_def] at htend
      exact h_not_left_end htend
    · intro p hp
      rw [moves_add] at hp
      rcases hp with ⟨nr, hnr, rfl⟩ | ⟨tr, htr, rfl⟩
      · -- `n ≥ 0` has no Right options.
        exfalso
        have hend : IsEnd Player.right ((n : ℤ) : GameForm) := isEnd_right_intCast_iff.mpr h_n
        rw [isEnd_def] at hend
        rw [hend] at hnr
        exact (Set.mem_empty_iff_false nr).mp hnr
      · -- `p = n + x gl`, a Left win.
        rw [htR] at htr; obtain ⟨⟨gl, hgl⟩, rfl⟩ := htr
        exact hx_n gl hgl

lemma maintenance_of_misereGE_left
    {g : GameForm} {n : ℤ} (h_n : 0 ≤ n)
    (h_g : PFreeDeadEnding g) (g_not_end : ¬IsEnd .left g)
    (h_ge : g ≥m PFreeDeadEnding (n + 1 : ℤ)) :
    Maintenance PFreeDeadEnding g !{{(n : GameForm)} | {1}} .left := by
  intro hl hhl
  apply Or.inl
  rw [leftMoves_ofSets, Set.mem_singleton_iff] at hhl
  subst hhl
  by_contra h_contra
  push_neg at h_contra
  have h_downlined := downlinked_intCast_of_not_leftMoves_misereGE h_g g_not_end h_n h_contra
  have h_mem : ((n : ℤ) : GameForm) ∈ moves .left ((n + 1 : ℤ) : GameForm) :=
    leftMoves_intCast_zero_le_succ h_n
  absurd h_downlined
  exact Form.not_downlinked_left_option_of_misereGE h_ge h_mem

lemma maintenance_of_misereGE_right
    {g : GameForm} {n : ℤ} (h_n : 0 ≤ n)
    (h_g : PFreeDeadEnding g) (h_ge : g ≥m PFreeDeadEnding (n + 1 : ℤ)) :
    Maintenance PFreeDeadEnding g !{{(n : GameForm)} | {1}} .right := by
  intro gr h_gr_mem
  by_contra h_contra
  push_neg at h_contra
  have : Downlinked PFreeDeadEnding gr ↑(n + 1) := by
    refine downlinked_intCast_of_not_leftMoves_misereGE (n := n + 1)
      (Hereditary.of_mem_moves h_g h_gr_mem) ?_ (by omega) ?_
    · intro hgr_left_end
      have hgr_not_ge : ¬ gr ≥m PFreeDeadEnding ((1 : ℤ) : GameForm) := by
        apply h_contra.left
        simp only [rightMoves_ofSets, Form.intCast_ofNat, Nat.cast_one, Set.mem_singleton_iff]
      obtain ⟨k, hk⟩ :=
        isEnd_left_exists_intCast_misereEQ (Hereditary.of_mem_moves h_g h_gr_mem) hgr_left_end
      have := (misereGE_rw_left (MisereEQ.symm hk) (PFreeDeadEnding.misereGE_of_int_le 1 (-(k : ℤ)) (by omega)))
      exact hgr_not_ge this
    · intro gl hgl h_gl_ge
      have := (misereGE_rw_right (reduction_a_one_int h_n) h_gl_ge)
      exact h_contra.right gl hgl this
  absurd this
  exact Form.not_downlinked_right_option_of_misereGE h_ge h_gr_mem

theorem misereGE_iff_promain_not_isEnd_left_int {g : GameForm} {n : ℤ} (h_n : 0 ≤ n)
    (h_g : PFreeDeadEnding g) (h_g_not_end : ¬IsEnd .left g) :
    (g ≥m PFreeDeadEnding (n + 1 : ℤ) ↔
      (Promain.Test PFreeDeadEnding g !{{(n : GameForm)} | {1}})) := by
  constructor
  · intro h_ge
    unfold Promain.Test
    have := misereGE_rw_right (reduction_a_one_int h_n) h_ge
    exact ⟨ maintenance_of_misereGE_right h_n h_g h_ge
          , maintenance_of_misereGE_left h_n h_g h_g_not_end h_ge
          , proviso_right_of_misereGE this
          , proviso_left_of_misereGE this
          ⟩
  · intro ⟨h1, h2, h3, h4⟩
    have := MisereEQ.symm (reduction_a_one_int h_n)
    apply misereGE_rw_right this
    refine Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding h1 h2 h3 h4

theorem zero_misereEQ_minusOne_one {A : GameForm → Prop} [IntegerInvertible A] :
    (0 : GameForm) =m A !{{(-1 : GameForm)} | {(1 : GameForm)}} := by
  have := IntegerInvertible.int_add_neg_misereEQ (A := A) 1
  apply MisereEQ.symm
  convert this
  ext p x
  cases p <;> simp

theorem misereGE_iff_promain_not_isEnd_left_zero {g : GameForm} {n : ℤ}
    (h_g : PFreeDeadEnding g) (h_g_not_end : ¬IsEnd .left g) :
    (g ≥m PFreeDeadEnding 0 ↔
      (Promain.Test PFreeDeadEnding g !{{-1} | {1}})) := by
  sorry
