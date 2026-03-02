module

public import CombinatorialGames.GameForm.Misere.Outcome
public import CombinatorialGames.Misere.DeadEnding
public import CombinatorialGames.Misere.PFree
public import CombinatorialGames.Misere.ShortUniverse

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
