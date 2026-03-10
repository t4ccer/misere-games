module

public import CombinatorialGames.Misere.DeadEnding
public import CombinatorialGames.Misere.Hereditary
public import CombinatorialGames.Misere.OutcomeStable
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
  p_free := IsPFree.mem_moves h.p_free h_mem
  dead_ending := IsDeadEnding.hereditary h.dead_ending h_mem

instance : PFree PFreeDeadEnding where
  pfree h := h.p_free

instance : ClosedUnderAddNat PFreeDeadEnding where
  has_add g n :=
    { p_free := IsPFree.add_nat g.p_free n
    , dead_ending := IsDeadEnding.add g.dead_ending (IsDeadEnding.nat n)
    }

instance : ClosedUnderNeg PFreeDeadEnding where
  neg_of g :=
    { p_free := ClosedUnderNeg.neg_iff.mpr g.p_free
    , dead_ending := ClosedUnderNeg.neg_iff.mpr g.dead_ending
    }

instance : HasNat PFreeDeadEnding where
  has_nat n :=
    { p_free := IsPFree.nat n
    , dead_ending := IsDeadEnding.nat n
    }

instance : HasInt PFreeDeadEnding where
  has_int n :=
    { p_free := IsPFree.int n
    , dead_ending := IsDeadEnding.int n
    }

private theorem outcome_eq_L_of_not_right_and_pfree {g : GameForm}
    (h_pfree : IsPFree g) (h_not_right : ¬WinsGoingFirst .right g) : MisereOutcome g = .L := by
  rw [MisereOutcome_eq_L_iff]
  refine ⟨?_, h_not_right⟩
  by_contra h_not_left
  exact PFree.MisereOutcome_ne_P h_pfree (MisereOutcome_eq_P_iff.mpr ⟨h_not_right, h_not_left⟩)

private theorem left_end_outcome_N_eq_zero {g : GameForm} (hg : PFreeDeadEnding g)
    (hN : MisereOutcome g = .N) (h_left_end : IsEnd .left g) : g = 0 := by
  by_contra h_ne_zero
  have h_left_dead := IsDeadEnding.IsDeadEnd hg.dead_ending h_left_end
  exact absurd (GameForm.lemma3_L g h_ne_zero h_left_dead) (by simp [hN])

mutual

private theorem outcome_LL_add_aux {g h : GameForm}
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
      · exact WinsGoingFirst_of_IsEnd (IsEnd.add_iff.mpr ⟨GameForm.IsEndLike_iff.mp hg_end, GameForm.IsEndLike_iff.mp  hh_end⟩)
      · have hhl_pfde := PFreeDeadEnding.of_move hh hhl
        have hhlL := outcome_eq_L_of_not_right_and_pfree hhl_pfde.p_free hhl_not_right
        have hsumL := outcome_LL_add_aux hg hhl_pfde hgL hhlL
        exact WinsGoingFirst_of_moves
          ⟨g + hl, add_left_mem_moves_add hhl g, (MisereOutcome_eq_L_iff.mp hsumL).right⟩
    · have hgl_pfde := PFreeDeadEnding.of_move hg hgl
      have hglL := outcome_eq_L_of_not_right_and_pfree hgl_pfde.p_free hgl_not_right
      have hsumL := outcome_LL_add_aux hgl_pfde hh hglL hhL
      exact WinsGoingFirst_of_moves
        ⟨gl + h, add_right_mem_moves_add hgl h, (MisereOutcome_eq_L_iff.mp hsumL).right⟩
  · rw [not_WinsGoingFirst]
    refine ⟨fun h_end => ?_, fun gr hgr => ?_⟩
    · exact hg_out.right (WinsGoingFirst_of_IsEnd (IsEnd.add_iff.mp (GameForm.IsEndLike_iff.mp  h_end)).left)
    · rw [moves_add, Set.mem_union, Set.mem_image] at hgr
      rcases hgr with ⟨gr', hgr', rfl⟩ | ⟨hr, hhr, rfl⟩
      · have h_left_gr' : WinsGoingFirst .left gr' := by
          simpa [Player.neg_right] using
            (not_WinsGoingFirst.mp hg_out.right).right gr' hgr'
        have hgr_pfde := PFreeDeadEnding.of_move hg hgr'
        cases hgr'_out : MisereOutcome gr' with
        | L => exact (MisereOutcome_eq_L_iff.mp (outcome_LL_add_aux hgr_pfde hh hgr'_out hhL)).left
        | N => exact add_comm h gr' ▸ MiserePlayerOutcome_eq_iff_WinsGoingFirst.mp
                 (player_outcome_LN_add_aux hh hgr_pfde hhL hgr'_out)
        | P => exact absurd hgr'_out (PFree.MisereOutcome_ne_P hgr_pfde)
        | R => exact absurd h_left_gr' (MisereOutcome_eq_R_iff.mp hgr'_out).right
      · have h_left_hr : WinsGoingFirst .left hr := by
          simpa [Player.neg_right] using
            (not_WinsGoingFirst.mp hh_out.right).right hr hhr
        have hhr_pfde := PFreeDeadEnding.of_move hh hhr
        cases hhr_out : MisereOutcome hr with
        | L => exact (MisereOutcome_eq_L_iff.mp (outcome_LL_add_aux hg hhr_pfde hgL hhr_out)).left
        | N => exact MiserePlayerOutcome_eq_iff_WinsGoingFirst.mp
                 (player_outcome_LN_add_aux hg hhr_pfde hgL hhr_out)
        | P => exact absurd hhr_out (PFree.MisereOutcome_ne_P hhr_pfde)
        | R => exact absurd h_left_hr (MisereOutcome_eq_R_iff.mp hhr_out).right
termination_by Form.birthday g + Form.birthday h
decreasing_by all_goals gameform_birthday

private theorem player_outcome_LN_add_aux {g h : GameForm}
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
    · exact absurd (GameForm.IsEndLike_iff.mp h_left_end) h_not_left_end
    · have hhl_pfde := PFreeDeadEnding.of_move hh hhl
      refine WinsGoingFirst_of_moves ⟨g + hl, add_left_mem_moves_add hhl g, ?_⟩
      refine (MisereOutcome_eq_L_iff.mp ?_).right
      apply outcome_LL_add_aux hg hhl_pfde hgL
      exact outcome_eq_L_of_not_right_and_pfree hhl_pfde.p_free hhl_not_right
termination_by Form.birthday g + Form.birthday h
decreasing_by gameform_birthday

end

private theorem outcome_RR_add_aux {g h : GameForm}
    (hg : PFreeDeadEnding g) (hh : PFreeDeadEnding h)
    (hgR : MisereOutcome g = .R) (hhR : MisereOutcome h = .R)
    : MisereOutcome (g + h) = .R := by
  rw [<-neg_MisereOutcome_L_iff]
  simpa [neg_add_rev, add_comm]
    using outcome_LL_add_aux
            (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
            ((neg_MisereOutcome_L_iff).mpr hgR) ((neg_MisereOutcome_L_iff).mpr hhR)

private theorem player_outcome_RN_add_aux {g h : GameForm}
    (hg : PFreeDeadEnding g) (hh : PFreeDeadEnding h)
    (hgR : MisereOutcome g = .R) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .right = .right := by
  rw [MiserePlayerOutcome_eq_iff_WinsGoingFirst, <-Player.neg_left, <-WinsGoingFirst_neg_iff]
  simpa [neg_add_rev, add_comm]
    using MiserePlayerOutcome_eq_iff_WinsGoingFirst.mp
          (player_outcome_LN_add_aux
            (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
            ((neg_MisereOutcome_L_iff).2 hgR) (neg_MisereOutcome_N_iff.mpr hhN))


instance : OutcomeStable PFreeDeadEnding where
  outcome_LL_add := outcome_LL_add_aux
  outcome_RR_add := outcome_RR_add_aux
  player_outcome_LN_add := player_outcome_LN_add_aux
  player_outcome_RN_add := player_outcome_RN_add_aux

namespace PFreeDeadEnding

theorem int_ordered (a b : ℤ) (h1 : a ≥ b) : b ≥m PFreeDeadEnding a :=
  OutcomeStable.MisereGe_of_int_le PFreeDeadEnding b a h1

theorem nat_ordered (a b : ℕ) (h1 : a ≥ b) : b ≥m PFreeDeadEnding a :=
  OutcomeStable.MisereGe_of_nat_le PFreeDeadEnding b a h1

theorem a_one_MisereOutcome {a : ℤ} (h0 : 0 ≤ a) : MisereOutcome (!{{(a : GameForm)} | {1}}) = .R := by
  refine MisereOutcome_eq_R_iff.mpr ?_
  apply And.intro
  · refine WinsGoingFirst_of_moves ⟨1, ?_⟩
    simp only [moves_ofSets, Set.mem_singleton_iff, Player.le_left, Player.neg_right, Player.le_left_eq, true_and]
    refine not_WinsGoingFirst.mpr ?_
    apply And.intro (by simp [IsEnd_def])
    simp
  · refine not_WinsGoingFirst.mpr ?_
    simp [IsEnd_def, h0]

theorem a_one_PFreeDeadEnding {a : ℤ} (h0 : 0 ≤ a) : PFreeDeadEnding (!{{(a : GameForm)} | {1}}) where
  p_free := by
    unfold IsPFree
    apply And.intro
    · simp [a_one_MisereOutcome, h0]
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

theorem reduction_a_one_int {a : ℤ} (h0 : 0 ≤ a)
    : (!{{(a : GameForm)} | {1}}) =m PFreeDeadEnding ((a + 1) : ℤ) := by
  have h0' : 0 ≤ a + 1 := Int.le_add_one h0
  have h0'' : 0 < a + 1 := Int.le_iff_lt_add_one.mp h0
  refine MisereGe_antisymm ?_ ?_
  · apply Hereditary.MisereGe PFreeDeadEnding
    · simpa [Maintenance, h0'] using int_ordered (a + 1) 0 h0'
    · simp only [Maintenance, moves_ofSets, Set.mem_singleton_iff, exists_eq_left]
      intro hl h_hl
      apply Or.inl
      have h_hl := eq_sub_one_of_mem_leftMoves_intCast h_hl
      rw [Int.add_sub_cancel a 1] at h_hl
      simp [h_hl]
    · simp [Proviso, IsEnd_def]
    · simp [Proviso, IsEnd_def, h0]
  · apply Hereditary.MisereGe PFreeDeadEnding
    · simp [Maintenance, h0']
    · simp [Maintenance, h0'']
    · simp [Proviso, Strong]
      intro _ x h2 h3
      have h4 : WinsGoingFirst .right x := WinsGoingFirst_of_IsEnd h3
      have h6 : MisereOutcome x ≤ .N := rightWinsGoingFirst_outcome_le_N h4
      apply Or.elim (Outcome.le_N_eq_N_or_R h6) <;> intro h7
      · rw [<-MiserePlayerOutcome_eq_iff_WinsGoingFirst]
        exact OutcomeStable.player_outcome_RN_add (a_one_PFreeDeadEnding h0) h2 (a_one_MisereOutcome h0) h7
      · apply MisereOutcome_R_eq_WinsGoingFirst
        exact OutcomeStable.outcome_RR_add (a_one_PFreeDeadEnding h0) h2 (a_one_MisereOutcome h0) h7
    · simp [Proviso, IsEnd_def]

private theorem reduction_ab_int.auxL {a b : ℤ} (h0 : 0 ≤ a) (h2 : 1 ≤ b) (h3 : b ≤ a + 2)
    : (!{{(a : GameForm)} | {(b : GameForm)}}) ≥m PFreeDeadEnding (!{{(a : GameForm)} | {(1 : GameForm)}}) := by
  apply Hereditary.MisereGe PFreeDeadEnding
  · simp only [Maintenance, moves_ofSets, Set.mem_singleton_iff, exists_eq_left, forall_eq]
    refine Or.inr ⟨((b - 1) : ℤ), leftMoves_intCast_zero_lt h2, ?_⟩
    exact MisereGe_rw_right (reduction_a_one_int h0) (int_ordered (a + 1) (b - 1) (by omega))
  · simp [Maintenance]
  · simp [Proviso, IsEnd_def]
  · simp [Proviso, IsEnd_def]

private theorem reduction_ab_int.auxR (a : ℤ) {b : ℤ} (h0 : 1 ≤ b)
    : (!{{(a : GameForm)} | {(1 : GameForm)}}) ≥m PFreeDeadEnding (!{{(a : GameForm)} | {(b : GameForm)}}) := by
  apply Hereditary.MisereGe PFreeDeadEnding
  · simp only [Maintenance, moves_ofSets, Set.mem_singleton_iff, exists_eq_left, forall_eq]
    apply Or.inl
    rw [<-GameForm.intCast_one]
    exact int_ordered b (1 : ℕ) h0
  · simp [Maintenance]
  · simp [Proviso, IsEnd_def]
  · simp [Proviso, IsEnd_def]

theorem reduction_ab_int (a b : ℤ) (h0 : 0 ≤ a) (h1 : 1 ≤ b) (h2 : b ≤ a + 2)
    : (!{{(a : GameForm)} | {(b : GameForm)}}) =m PFreeDeadEnding ((a + 1) : ℤ) := by
  refine MisereEq_trans ?_ (reduction_a_one_int h0)
  apply MisereGe_antisymm (reduction_ab_int.auxL h0 h1 h2) (reduction_ab_int.auxR a h1)

lemma MisereOutcome_L_Strong {A : GameForm → Prop} [PFree A] [OutcomeStable A] {g : GameForm}
    (h1 : A g) (h2 : MisereOutcome g = .L) : Strong A g .left := by
  intro x hx h3
  apply Or.elim (PFree.IsEnd_left_MisereOutcome hx (GameForm.IsEndLike_iff.mp h3)) <;> intro h5
  · apply Or.elim (OutcomeStable.outcome_LN_add h1 hx h2 h5) <;> intro h6
    · rw [<-MiserePlayerOutcome_eq_iff_WinsGoingFirst]
      exact (MisereOutcome_N_iff_MiserePlayerOutcome.mp h6).left
    · exact MisereOutcome_L_eq_WinsGoingFirst h6
  · exact MisereOutcome_L_eq_WinsGoingFirst (OutcomeStable.outcome_LL_add h1 hx h2 h5)

lemma MisereOutcome_R_Strong {A : GameForm → Prop} [PFree A] [OutcomeStable A] {g : GameForm}
    (h1 : A g) (h2 : MisereOutcome g = .R) : Strong A g .right := by
  intro x hx h3
  apply Or.elim (PFree.IsEnd_right_MisereOutcome hx (GameForm.IsEndLike_iff.mp h3)) <;> intro h5
  · apply Or.elim (OutcomeStable.outcome_RN_add h1 hx h2 h5) <;> intro h6
    · rw [<-MiserePlayerOutcome_eq_iff_WinsGoingFirst]
      exact (MisereOutcome_N_iff_MiserePlayerOutcome.mp h6).right
    · exact MisereOutcome_R_eq_WinsGoingFirst h6
  · exact MisereOutcome_R_eq_WinsGoingFirst (OutcomeStable.outcome_RR_add h1 hx h2 h5)

theorem PFreeDeadEnding_Proviso_iff_DeadEnding_Proviso {g h : GameForm} {p : Player}
    : Proviso PFreeDeadEnding g h p ↔ Proviso IsDeadEnding g h p := by
  apply Iff.intro <;> intro h1
  · intro h2 x h3 h4
    have h5 : PFreeDeadEnding x :=
      { p_free := IsDeadEnd.IsPFree (IsDeadEnding.IsDeadEnd h3 (GameForm.IsEndLike_iff.mp h4))
      , dead_ending := h3
      }
    exact h1 h2 x h5 h4
  · intro h2 x h3 h4
    exact h1 h2 x h3.dead_ending h4

private theorem reduction_ab_between_int_left.aux {a b : ℤ} (h0 : 0 ≤ a) (h1 : a + 2 ≤ b)
    : !{{(a : GameForm)}|{(b : GameForm)}} ≥m PFreeDeadEnding !{{((b - 2 : ℤ) : GameForm)}|{1}} := by
  apply Hereditary.MisereGe PFreeDeadEnding
  · simp only [Maintenance, moves_ofSets, Set.mem_singleton_iff, exists_eq_left, forall_eq]
    refine Or.inr ⟨(b - 1 : ℤ), leftMoves_intCast_zero_lt (by omega), ?_⟩
    have h2 := reduction_ab_int (b - 2) 1 (by omega) Int.le_rfl (by omega)
    rw [intCast_ofNat, Nat.cast_one] at h2
    apply MisereGe_rw_right h2
    have h3 : b - 2 + 1 = b - 1 := by omega
    rw [h3]
    exact MisereGe_refl _
  · simp only [Maintenance, moves_ofSets, Set.mem_singleton_iff, exists_eq_left, forall_eq]
    exact Or.inl (int_ordered (b - 2) a (by omega))
  · simp [Proviso, IsEnd_def]
  · simp [Proviso, IsEnd_def]

theorem reduction_ab_between_int_left {a b : ℤ} (h0 : 0 ≤ a) (h1 : a + 2 ≤ b)
    : !{{(a : GameForm)}|{(b : GameForm)}} ≥m PFreeDeadEnding ((b - 1 : ℤ) : GameForm) := by
  refine MisereGe_rw_right (MisereEq_symm ?_) (reduction_ab_between_int_left.aux h0 h1)
  have h2 := reduction_ab_int (b - 2) 1 (by omega) Int.le_rfl (by omega)
  have h4 : b - 2 + 1 = b - 1 := by omega
  rwa [intCast_ofNat, Nat.cast_one, h4] at h2

theorem reduction_ab_between_int_right {a b : ℤ} (h0 : 0 ≤ a) (h1 : 1 ≤ b)
    : ((a + 1 : ℤ) : GameForm) ≥m PFreeDeadEnding !{{(a : GameForm)}|{(b : GameForm)}} := by
  refine MisereGe_rw_left ?_ (reduction_ab_int.auxR a h1)
  have h2 := reduction_ab_int a 1 h0 Int.le_rfl (by omega)
  norm_cast at h2
