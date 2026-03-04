module

public import CombinatorialGames.Misere.DeadEnding
public import CombinatorialGames.Misere.Hereditary
public import CombinatorialGames.Misere.PFree

public section

universe u

open Form
open Form.Misere.Outcome
open GameForm.Misere.Outcome
open GameForm
open MisereForm

structure PFreeDeadEnding (g : GameForm) : Prop where
  p_free : IsPFree g
  dead_ending : IsDeadEnding g

private theorem PFreeDeadEnding.of_move {g gp : GameForm} {p : Player}
    (h : PFreeDeadEnding g) (h_mem : gp ∈ moves p g) : PFreeDeadEnding gp where
  p_free := IsPFree_moves h.p_free h_mem
  dead_ending := IsDeadEnding.hereditary h.dead_ending h_mem

private theorem PFreeDeadEnding.neg {g : GameForm} (h : PFreeDeadEnding g) : PFreeDeadEnding (-g) where
  p_free := IsPFree.neg_iff.mpr h.p_free
  dead_ending := IsDeadEnding.neg_iff.mpr h.dead_ending

private theorem outcome_eq_L_of_not_right_and_pfree {g : GameForm}
    (h_pfree : IsPFree g) (h_not_right : ¬WinsGoingFirst .right g) : MisereOutcome g = .L := by
  rw [MisereOutcome_eq_L_iff]
  refine ⟨?_, h_not_right⟩
  by_contra h_not_left
  exact h_pfree.MisereOutcome_ne_P (MisereOutcome_eq_P_iff.mpr ⟨h_not_right, h_not_left⟩)

private theorem left_end_outcome_N_eq_zero {g : GameForm} (hg : PFreeDeadEnding g)
    (hN : MisereOutcome g = .N) (h_left_end : IsEnd .left g) : g = 0 := by
  by_contra h_ne_zero
  have h_left_dead := IsDeadEnding.IsDeadEnd hg.dead_ending h_left_end
  exact absurd (GameForm.lemma3_L g h_ne_zero h_left_dead) (by simp [hN])

mutual

private theorem outcome_LL_add_aux (g h : GameForm)
    (hg : PFreeDeadEnding g) (hh : PFreeDeadEnding h)
    (hgL : MisereOutcome g = .L) (hhL : MisereOutcome h = .L) :
    MisereOutcome (g + h) = .L := by
  have hg_out := MisereOutcome_eq_L_iff.mp hgL
  have hh_out := MisereOutcome_eq_L_iff.mp hhL
  refine MisereOutcome_eq_L_iff.mpr ⟨?_, ?_⟩
  · rcases (WinsGoingFirst_iff g .left).mp hg_out.left with
        hg_end | ⟨gl, hgl, hgl_not_right⟩
    · rcases (WinsGoingFirst_iff h .left).mp hh_out.left with
          hh_end | ⟨hl, hhl, hhl_not_right⟩
      · exact WinsGoingFirst_of_End (IsEnd.add_iff.mpr ⟨hg_end, hh_end⟩)
      · have hhl_pfde := PFreeDeadEnding.of_move hh hhl
        have hhlL := outcome_eq_L_of_not_right_and_pfree hhl_pfde.p_free hhl_not_right
        have hsumL := outcome_LL_add_aux g hl hg hhl_pfde hgL hhlL
        exact WinsGoingFirst_of_moves
          ⟨g + hl, add_left_mem_moves_add hhl g, (MisereOutcome_eq_L_iff.mp hsumL).right⟩
    · have hgl_pfde := PFreeDeadEnding.of_move hg hgl
      have hglL := outcome_eq_L_of_not_right_and_pfree hgl_pfde.p_free hgl_not_right
      have hsumL := outcome_LL_add_aux gl h hgl_pfde hh hglL hhL
      exact WinsGoingFirst_of_moves
        ⟨gl + h, add_right_mem_moves_add hgl h, (MisereOutcome_eq_L_iff.mp hsumL).right⟩
  · rw [not_WinsGoingFirst]
    refine ⟨fun h_end => ?_, fun gr hgr => ?_⟩
    · exact hg_out.right (WinsGoingFirst_of_End (IsEnd.add_iff.mp h_end).left)
    · rw [moves_add, Set.mem_union, Set.mem_image] at hgr
      rcases hgr with ⟨gr', hgr', rfl⟩ | ⟨hr, hhr, rfl⟩
      · have h_left_gr' : WinsGoingFirst .left gr' := by
          simpa [Player.neg_right] using
            (not_WinsGoingFirst.mp hg_out.right).right gr' hgr'
        have hgr_pfde := PFreeDeadEnding.of_move hg hgr'
        cases hgr'_out : MisereOutcome gr' with
        | L => exact (MisereOutcome_eq_L_iff.mp (outcome_LL_add_aux gr' h hgr_pfde hh hgr'_out hhL)).left
        | N => exact add_comm h gr' ▸ MiserePlayerOutcome_eq_iff_WinsGoingFirst.mp
                 (player_outcome_LN_add_aux h gr' hh hgr_pfde hhL hgr'_out)
        | P => exact absurd hgr'_out hgr_pfde.p_free.MisereOutcome_ne_P
        | R => exact absurd h_left_gr' (MisereOutcome_eq_R_iff.mp hgr'_out).right
      · have h_left_hr : WinsGoingFirst .left hr := by
          simpa [Player.neg_right] using
            (not_WinsGoingFirst.mp hh_out.right).right hr hhr
        have hhr_pfde := PFreeDeadEnding.of_move hh hhr
        cases hhr_out : MisereOutcome hr with
        | L => exact (MisereOutcome_eq_L_iff.mp (outcome_LL_add_aux g hr hg hhr_pfde hgL hhr_out)).left
        | N => exact MiserePlayerOutcome_eq_iff_WinsGoingFirst.mp
                 (player_outcome_LN_add_aux g hr hg hhr_pfde hgL hhr_out)
        | P => exact absurd hhr_out hhr_pfde.p_free.MisereOutcome_ne_P
        | R => exact absurd h_left_hr (MisereOutcome_eq_R_iff.mp hhr_out).right
termination_by Form.birthday g + Form.birthday h
decreasing_by
  all_goals (
    have := Form.birthday_lt_of_mem_moves (by assumption)
    first
    | exact add_lt_add_right this _
    | exact add_lt_add_left this _
    | simpa [add_comm, add_left_comm, add_assoc] using
        (add_lt_add_left this (Form.birthday h)))

private theorem player_outcome_LN_add_aux (g h : GameForm)
    (hg : PFreeDeadEnding g) (hh : PFreeDeadEnding h)
    (hgL : MisereOutcome g = .L) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .left = .left := by
  rw [MiserePlayerOutcome_eq_iff_WinsGoingFirst]
  by_cases h_zero : h = 0
  · subst h
    simpa [add_zero] using (MisereOutcome_eq_L_iff.mp hgL).left
  · have h_not_left_end : ¬IsEnd .left h :=
      fun h_left_end => h_zero (left_end_outcome_N_eq_zero hh hhN h_left_end)
    rcases (WinsGoingFirst_iff h .left).mp (MisereOutcome_eq_N_iff.mp hhN).left with
        h_left_end | ⟨hl, hhl, hhl_not_right⟩
    · exact absurd h_left_end h_not_left_end
    · have hhl_pfde := PFreeDeadEnding.of_move hh hhl
      have hhlL := outcome_eq_L_of_not_right_and_pfree hhl_pfde.p_free hhl_not_right
      have hsumL := outcome_LL_add_aux g hl hg hhl_pfde hgL hhlL
      exact WinsGoingFirst_of_moves
        ⟨g + hl, add_left_mem_moves_add hhl g, (MisereOutcome_eq_L_iff.mp hsumL).right⟩
termination_by Form.birthday g + Form.birthday h
decreasing_by
  all_goals (
    have := Form.birthday_lt_of_mem_moves (by assumption)
    exact add_lt_add_right this _)

end

private theorem outcome_RR_add_aux (g h : GameForm)
    (hg : PFreeDeadEnding g) (hh : PFreeDeadEnding h)
    (hgR : MisereOutcome g = .R) (hhR : MisereOutcome h = .R) :
    MisereOutcome (g + h) = .R := by
  have h_neg_g_L : MisereOutcome (-g) = .L := (neg_MisereOutcome_L_iff).2 hgR
  have h_neg_h_L : MisereOutcome (-h) = .L := (neg_MisereOutcome_L_iff).2 hhR
  have h_neg_sum_L : MisereOutcome ((-g) + (-h)) = .L :=
    outcome_LL_add_aux (-g) (-h) hg.neg hh.neg h_neg_g_L h_neg_h_L
  exact (neg_MisereOutcome_L_iff).1 (by
    simpa [neg_add_rev, add_comm] using h_neg_sum_L)

private theorem player_outcome_RN_add_aux (g h : GameForm)
    (hg : PFreeDeadEnding g) (hh : PFreeDeadEnding h)
    (hgR : MisereOutcome g = .R) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .right = .right := by
  have h_neg_g_L : MisereOutcome (-g) = .L := (neg_MisereOutcome_L_iff).2 hgR
  have h_neg_h_N : MisereOutcome (-h) = .N := neg_MisereOutcome_N_iff.mpr hhN
  have h_neg_wgf : WinsGoingFirst .left ((-g) + (-h)) :=
    MiserePlayerOutcome_eq_iff_WinsGoingFirst.mp
      (player_outcome_LN_add_aux (-g) (-h) hg.neg hh.neg h_neg_g_L h_neg_h_N)
  rw [MiserePlayerOutcome_eq_iff_WinsGoingFirst]
  exact (WinsGoingFirst_neg_iff (g + h) .left).mp (by
    simpa [neg_add_rev, add_comm] using h_neg_wgf)

instance : OutcomeStable PFreeDeadEnding where
  outcome_LL_add := outcome_LL_add_aux
  outcome_RR_add := outcome_RR_add_aux
  player_outcome_LN_add := player_outcome_LN_add_aux
  player_outcome_RN_add := player_outcome_RN_add_aux

instance : PFree PFreeDeadEnding where
  pfree h := h.p_free

instance : ClosedUnderAddNat PFreeDeadEnding where
  has_add g n :=
    { p_free := add_nat_IsPFree g.p_free n
    , dead_ending := IsDeadEnding.add g.dead_ending (IsDeadEnding.nat n)
    }

instance : HasOne PFreeDeadEnding where
  has_one' :=
    { p_free := IsPFree.one
    , dead_ending := IsDeadEnding.one
    }

instance : HasNat PFreeDeadEnding where
  has_nat n :=
    { p_free := IsPFree.nat n
    , dead_ending := IsDeadEnding.nat n
    }

namespace PFreeDeadEnding

@[simp]
theorem nat_ordered (a b : ℕ) (h1 : a ≥ b) : b ≥m PFreeDeadEnding a :=
  MisereGe_of_nat_le PFreeDeadEnding b a h1

theorem a_one_MisereOutcome (a : ℕ) : MisereOutcome (!{{(a : GameForm)} | {1}}) = .R := by
  refine MisereOutcome_eq_R_iff.mpr ?_
  apply And.intro
  · refine WinsGoingFirst_of_moves ?_
    use 1
    simp
    refine not_WinsGoingFirst.mpr ?_
    apply And.intro (by simp [IsEnd_def])
    simp
  · refine not_WinsGoingFirst.mpr ?_
    simp [IsEnd_def]

theorem a_one_PFreeDeadEnding (a : ℕ) : PFreeDeadEnding (!{{(a : GameForm)} | {1}}) where
  p_free := by
    unfold IsPFree
    apply And.intro
    · simp [a_one_MisereOutcome]
    · intro p; cases p <;> simp
  dead_ending := by
    unfold IsDeadEnding
    apply And.intro <;> intro p <;> cases p
    · simp [IsEnd_def]
    · simp [IsEnd_def]
    · simp
    · simp

instance : Hereditary PFreeDeadEnding where
  has_option h1 h2 :=
    { p_free := IsPFree.IsOption h1.p_free h2
    , dead_ending := IsDeadEnding.IsOption h1.dead_ending h2
    }

-- TODO: Fix writeup from 0 to 1
theorem reduction_a_one_int (a : ℕ) : (!{{(a : GameForm)} | {1}}) =m PFreeDeadEnding ((a + 1) : ℕ) := by
  refine MisereGe_antisymm ?_ ?_
  · apply Hereditary.MisereGe PFreeDeadEnding
    · simp [Maintenance]
      exact nat_ordered (a + 1) 0 (Nat.le_add_left 0 (a + 1))
    · simp [Maintenance]
    · simp [Proviso, IsEnd_def]
    · simp [Proviso, IsEnd_def]
  · apply Hereditary.MisereGe PFreeDeadEnding
    · simp [Maintenance]
    · simp [Maintenance]
    · simp [Proviso, Strong]
      intro x h2 h3
      have h4 : WinsGoingFirst .right x := WinsGoingFirst_of_End h3
      have h6 : MisereOutcome x ≤ .N := rightWinsGoingFirst_outcome_le_N h4
      apply Or.elim (Outcome.le_N_eq_N_or_R h6) <;> intro h7
      · have h8 := OutcomeStable.player_outcome_RN_add _ _ (a_one_PFreeDeadEnding a) h2 (a_one_MisereOutcome a) h7
        simp at h8
        exact h8
      · have h8 := OutcomeStable.outcome_RR_add _ _ (a_one_PFreeDeadEnding a) h2 (a_one_MisereOutcome a) h7
        simp [h8]
    · simp [Proviso, IsEnd_def]

private theorem reduction_ab_int.aux {a b : ℕ} (h2 : 1 ≤ b) (h3 : b ≤ a + 2)
    : (!{{(a : GameForm)} | {(b : GameForm)}}) =m PFreeDeadEnding (!{{(a : GameForm)} | {(1 : GameForm)}}) := by
  refine MisereGe_antisymm ?_ ?_
  · apply Hereditary.MisereGe PFreeDeadEnding
    · simp [Maintenance]
      apply Or.inr
      use ((b - 1) : ℕ)
      apply And.intro
      · rw [<-Nat.succ_pred_eq_of_pos h2, leftMoves_natCast_succ']
        simp
      · apply MisereGe_rw_right (reduction_a_one_int a)
        exact nat_ordered (a + 1) (b - 1) (by omega)
    · simp [Maintenance]
    · simp [Proviso, IsEnd_def]
    · simp [Proviso, IsEnd_def]
  · apply Hereditary.MisereGe PFreeDeadEnding
    · simp [Maintenance]
      apply Or.inl
      rw [<-GameForm.intCast_one]
      exact nat_ordered b (1 : ℕ) (by omega)
    · simp [Maintenance]
    · simp [Proviso, IsEnd_def]
    · simp [Proviso, IsEnd_def]

theorem reduction_ab_int (a b : ℕ) (h2 : 1 ≤ b) (h3 : b ≤ a + 2)
    : (!{{(a : GameForm)} | {(b : GameForm)}}) =m PFreeDeadEnding ((a + 1) : ℕ) := by
  exact MisereEq_trans (reduction_ab_int.aux h2 h3) (reduction_a_one_int a)
