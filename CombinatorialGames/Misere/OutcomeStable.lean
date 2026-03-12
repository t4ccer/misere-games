module

public import CombinatorialGames.Misere.PFree

open Form
open Form.Misere.Outcome
open GameForm

universe u

public section

class OutcomeStable {G : Type (u + 1)} [Form G] (A : G → Prop) where
  outcome_LL_add {g h : G} (h1 : A g) (h2 : A h) (h3 : MisereOutcome g = .L) (h4 : MisereOutcome h = .L) :
    MisereOutcome (g + h) = .L
  outcome_RR_add {g h : G} (h1 : A g) (h2 : A h) (h3 : MisereOutcome g = .R) (h4 : MisereOutcome h = .R) :
    MisereOutcome (g + h) = .R
  player_outcome_LN_add {g h : G} (h1 : A g) (h2 : A h) (h3 : MisereOutcome g = .L) (h4 : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .left = .left
  player_outcome_RN_add {g h : G} (h1 : A g) (h2 : A h) (h3 : MisereOutcome g = .R) (h4 : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .right = .right

namespace OutcomeStable

theorem outcome_LN_add {G : Type (u + 1)} [Form G] {A : G → Prop} [OutcomeStable A]
    {g h : G} (h1 : A g) (h2 : A h) (h3 : MisereOutcome g = .L) (h4 : MisereOutcome h = .N) :
    MisereOutcome (g + h) = .N ∨ MisereOutcome (g + h) = .L := by
  have h5 := player_outcome_LN_add h1 h2 h3 h4
  simp only [MisereOutcome, Outcome.ofPlayers, h5]
  cases MiserePlayerOutcome (g + h) Player.right
  <;> simp only [reduceCtorEq, or_true, or_false]

theorem outcome_RN_add {G : Type (u + 1)} [Form G] {A : G → Prop} [OutcomeStable A]
    {g h : G} (h1 : A g) (h2 : A h) (h3 : MisereOutcome g = .R) (h4 : MisereOutcome h = .N) :
    MisereOutcome (g + h) = .N ∨ MisereOutcome (g + h) = .R := by
  have h5 := player_outcome_RN_add h1 h2 h3 h4
  simp only [MisereOutcome, Outcome.ofPlayers, h5]
  cases MiserePlayerOutcome (g + h) Player.left
  <;> simp only [reduceCtorEq, or_true, or_false]

@[simp]
theorem zero_ge_one {A : GameForm → Prop}
    [HasNat A] [OutcomeStable A] [PFree A] :
    0 ≥m A 1 := by
  rw [Misere.Outcome.MisereGe]
  intro x h1
  rw [zero_add]
  cases h2 : MisereOutcome x
  · exact Outcome.L_ge (MisereOutcome (1 + x))
  · have h3 := OutcomeStable.outcome_RN_add has_one h1 Misere.Outcome.one_MisereOutcome_R h2
    apply Or.elim h3 <;> intro h3 <;> simp only [h3, ge_iff_le, le_refl, Outcome.ge_R]
  · exact False.elim (PFree.MisereOutcome_ne_P h1 h2)
  · have h3 := OutcomeStable.outcome_RR_add has_one h1 Misere.Outcome.one_MisereOutcome_R h2
    rw [h3]

theorem ge_one_add_nat (A : GameForm → Prop)
    [OutcomeStable A] [PFree A] [ClosedUnderAddNat A] [HasNat A]
    (n : ℕ) : n ≥m A (((1 : ℕ) + n) : ℕ) := by
  by_cases h1 : n > 0
  · rw [Misere.Outcome.MisereGe]
    intro x h2
    simp only [Nat.cast_add, Nat.cast_one]
    rw [add_assoc _ _ x]
    nth_rw 2 [add_comm]
    cases h3 : MisereOutcome x
    · cases h4 : MisereOutcome (↑n + x)
      · simp only [ge_iff_le, Outcome.L_ge]
      · have h4' : A (n + x) := by
          have := (ClosedUnderAddNat.has_add h2 n)
          rwa [add_comm] at this
        have h5 := OutcomeStable.outcome_RN_add (A := A)
          has_one h4'
          Misere.Outcome.one_MisereOutcome_R h4
        rw [add_comm]
        apply Or.elim h5 <;> intro h5 <;> simp only [ge_iff_le, Outcome.ge_R, le_refl, h5]
      · exact False.elim (PFree.MisereOutcome_ne_P ((IsPFree.nat_add (PFree.pfree h2)) n) h4)
      · simp only [ge_iff_le, Outcome.le_R_iff]
        exact PFree.MisereOutcome_add_one_R (IsPFree.nat_add (PFree.pfree h2) n) h4
    · have h4 := OutcomeStable.outcome_RN_add
        (HasNat.has_nat n) h2
        (Misere.Outcome.pos_nat_MisereOutcome_R h1) h3
      apply Or.elim h4 <;> intro h4
      · have h4' : A (n + x) := by
          have := (ClosedUnderAddNat.has_add h2 n)
          rwa [add_comm] at this
        have h5 := OutcomeStable.outcome_RN_add
          has_one h4'
          (Misere.Outcome.one_MisereOutcome_R) h4
        nth_rw 2 [add_comm]
        aesop
      · simp_all only [gt_iff_lt, reduceCtorEq, or_true, ge_iff_le, Outcome.le_R_iff]
        exact PFree.MisereOutcome_add_one_R (IsPFree.nat_add (PFree.pfree h2) n) h4
    · refine False.elim (PFree.MisereOutcome_ne_P h2 h3)
    · have h4 := OutcomeStable.outcome_RR_add
         (HasNat.has_nat n) h2
         (Misere.Outcome.pos_nat_MisereOutcome_R h1) h3
      simp only [ge_iff_le, Outcome.le_R_iff, h4]
      exact PFree.MisereOutcome_add_one_R (IsPFree.nat_add (PFree.pfree h2) n) h4
  · simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h1
    simp only [h1, Nat.cast_zero, add_zero, Nat.cast_one, OutcomeStable.zero_ge_one]

theorem MisereGe_of_nat_le (A : GameForm → Prop)
    [OutcomeStable A] [PFree A] [ClosedUnderAddNat A] [HasNat A]
    (n m : ℕ) (h1 : n ≤ m) : n ≥m A m := by
  let k := m - n
  have h0 : m = n + k := by omega
  rw [h0]
  induction k with
  | zero => simp only [add_zero, Misere.Outcome.MisereGe_refl]
  | succ k' ih =>
    apply Misere.Outcome.MisereGe_trans ih
    rw [<-add_assoc, add_comm (n + k') 1]
    exact ge_one_add_nat A (n + k')

theorem ge_one_add_int (A : GameForm → Prop)
    [OutcomeStable A] [PFree A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (n : ℤ) : n ≥m A (((1 : ℤ) + n) : ℤ) := by
  by_cases h1 : n ≥ 0
  · obtain ⟨n', h_n'⟩ := (CanLift.prf n h1 : ∃ (n' : ℕ), n' = n)
    have h2 := ge_one_add_nat A n'
    rwa [<-intCast_nat, h_n',
         <-intCast_nat, Nat.cast_add, h_n', Nat.cast_one] at h2
  · have : ∃ (n' : ℕ), n' = -n := by
      use n.natAbs; exact Int.ofNat_natAbs_of_nonpos (by omega)
    obtain ⟨n', h_n'⟩ := this
    have h2 := ge_one_add_nat A (n' - 1)
    have h3 : 1 + (n' - 1) = n' := by omega
    rw [h3] at h2
    rw [<-intCast_nat, Nat.cast_sub (by omega), h_n',
        <-intCast_nat, h_n',
        <-Misere.Outcome.ClosedUnderNeg.neg_ge_neg_iff] at h2
    simp only [intCast_neg, neg_neg, Nat.cast_one] at h2
    rw [<-intCast_neg] at h2
    simp only [neg_sub, sub_neg_eq_add] at h2
    exact h2

theorem ge_nat_add_int (A : GameForm → Prop)
    [OutcomeStable A] [PFree A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (n : ℕ) (k : ℤ) : k ≥m A ((n + k) : ℤ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    simp
    have h1 : m + 1 + k = 1 + (m + k) := by omega
    rw [h1]
    exact Misere.Outcome.MisereGe_trans ih (ge_one_add_int A (m + k))

theorem MisereGe_of_int_le (A : GameForm → Prop)
    [OutcomeStable A] [PFree A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (n m : ℤ) (h1 : n ≤ m) : n ≥m A m := by
  obtain ⟨k, h_k⟩ := Int.le.dest h1
  rw [<-h_k, add_comm]
  exact ge_nat_add_int A k n
