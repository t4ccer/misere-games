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

instance : OutcomeStable PFreeDeadEnding where
   outcome_LL_add := sorry
   outcome_RR_add := sorry
   player_outcome_LN_add := sorry
   player_outcome_RN_add := sorry

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
