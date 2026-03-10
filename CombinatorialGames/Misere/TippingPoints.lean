module

public import CombinatorialGames.GameForm.Misere.Outcome
public import CombinatorialGames.Form.Short

open Form
open Form.Misere.Outcome
open MisereForm

universe u

public section

mutual

private theorem right_wins_of_birthday_le (g : GameForm) (b : ℕ) (h1 : birthday g ≤ b) :
    WinsGoingFirst .right (g + b) := by
  by_cases h2 : IsEnd .right g
  · exact add_end_WinsGoingFirst h2 (GameForm.nat_IsEnd_right b)
  · obtain ⟨gr, h3⟩ := Form.not_IsEnd_exists_move h2
    refine WinsGoingFirst_of_moves ?_
    refine ⟨gr + b, Form.add_right_mem_moves_add h3 b, ?_⟩
    exact not_left_wins_of_birthday_lt gr b ((Form.birthday_lt_of_mem_moves h3).trans_le h1)
termination_by g
decreasing_by form_wf

private theorem not_left_wins_of_birthday_lt (g : GameForm) (b : ℕ) (h1 : birthday g < b) :
    ¬WinsGoingFirst .left (g + b) := by
  have hbpos : 0 < b := by
    by_contra hb
    have : b = 0 := Nat.eq_zero_of_not_pos hb
    subst this
    simp at h1
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hbpos)
  rw [not_WinsGoingFirst]
  constructor
  · intro h2
    rw [GameForm.IsEndLike_iff] at h2
    have h4 : ¬IsEnd .left ((k + 1 : ℕ) : GameForm) := by simp [IsEnd_def]
    exact h4 (by simpa [hk] using (IsEnd.add_iff.mp h2).right)
  · intro gl h2
    rw [moves_add] at h2
    rcases h2 with ⟨gl', h3, rfl⟩ | ⟨bl, h3, rfl⟩
    · exact right_wins_of_birthday_le gl' b (((Form.birthday_lt_of_mem_moves h3).trans h1).le)
    · have h6 : bl = (k : GameForm) := by
        simpa [hk, Nat.succ_eq_add_one] using h3
      rw [h6]
      have h7 : birthday g ≤ (k : ℕ) := by
        apply Order.lt_add_one_iff.mp
        simpa [hk, Nat.cast_add, Nat.cast_one] using h1
      by_cases h8 : IsEnd .right g
      · exact add_end_WinsGoingFirst h8 (GameForm.nat_IsEnd_right k)
      · obtain ⟨gr, h9⟩ := Form.not_IsEnd_exists_move h8
        refine WinsGoingFirst_of_moves ?_
        refine ⟨gr + k, Form.add_right_mem_moves_add h9 k, ?_⟩
        exact not_left_wins_of_birthday_lt gr k ((Form.birthday_lt_of_mem_moves h9).trans_le h7)
termination_by g
decreasing_by form_wf

end

private theorem add_gt_birthday_R (g : GameForm) (b : ℕ) (h1 : birthday g < b) :
    MisereOutcome (g + b) = .R := by
  exact MisereOutcome_eq_R_iff.mpr
    ⟨right_wins_of_birthday_le g b h1.le, not_left_wins_of_birthday_lt g b h1⟩

theorem add_birthday_plus_one_R (g : GameForm) (b : ℕ) (h1 : birthday g = b) :
    MisereOutcome (g + (b + (1 : ℕ))) = .R := by
  have h2 : (b : NatOrdinal) < (b + 1 : ℕ) := by
    simp
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using add_gt_birthday_R g (b + 1) (h1 ▸ h2)

theorem add_neg_birthday_plus_one_L (g : GameForm) (b : ℕ) (h1 : birthday g = b) :
    MisereOutcome (g + (-(b + (1 : ℕ)))) = .L := by
  simpa [outcome_conjugate_eq_outcome_neg, neg_add_rev, add_comm, add_left_comm, add_assoc] using
    congrArg Outcome.Conjugate
      (add_birthday_plus_one_R (-g) b (by simpa [Form.birthday_neg] using h1))

def RTippingPoint.aux (g : GameForm) [h1 : Short g] :
    ∃ (n : ℕ), MisereOutcome (g + n) = .R := by
  let ⟨b, h2⟩ := GameForm.short_iff_birthday_nat.mp h1
  use (b + 1)
  rw [Nat.cast_add]
  exact add_birthday_plus_one_R g b h2

def LTippingPoint.aux (g : GameForm) [h1 : Short g] :
    ∃ (n : ℕ), MisereOutcome (g + (-n)) = .L := by
  let ⟨b, h2⟩ := GameForm.short_iff_birthday_nat.mp h1
  use (b + 1)
  rw [Nat.cast_add]
  exact add_neg_birthday_plus_one_L g b h2

private theorem left_wins_second_implies_left_wins_first_add_one {g : GameForm}
    (h1 : ¬WinsGoingFirst .right g) : WinsGoingFirst .left (g + 1) := by
  refine WinsGoingFirst_of_moves ?_
  refine ⟨g, ?_, ?_⟩
  · rw [moves_add, GameForm.leftMoves_one]
    right
    refine ⟨0, by simp, by simp⟩
  · simpa [Player.neg_left] using h1

private theorem exists_add_nat_N_of_not_R (g : GameForm) [Short g] (h1 : MisereOutcome g ≠ .R) :
    ∃ n : ℕ, MisereOutcome (g + n) = .N := by
  let hR : ∃ n : ℕ, MisereOutcome (g + n) = .R := RTippingPoint.aux g
  let r : ℕ := Nat.find hR
  have hrR : MisereOutcome (g + r) = .R := Nat.find_spec hR
  have hrpos : 0 < r := by
    by_contra h2
    have h3 : r = 0 := Nat.eq_zero_of_not_pos h2
    exact h1 (by simpa [r, h3, Nat.cast_zero, add_zero] using hrR)
  let n : ℕ := r - 1
  have hnsucc : n + 1 = r := by
    dsimp [n]
    omega
  have hnlt : n < r := by
    omega
  have hnotR_n : MisereOutcome (g + n) ≠ .R := by
    exact Nat.find_min hR (by simpa [r] using hnlt)
  have hnotLeft_r : ¬WinsGoingFirst .left (g + r) := (MisereOutcome_eq_R_iff.mp hrR).2
  have hright_n : WinsGoingFirst .right (g + n) := by
    by_contra h2
    have h3 : WinsGoingFirst .left ((g + n) + 1) :=
      left_wins_second_implies_left_wins_first_add_one h2
    have h4 : WinsGoingFirst .left (g + (n + 1 : ℕ)) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using h3
    exact hnotLeft_r (by simpa [hnsucc] using h4)
  refine ⟨n, ?_⟩
  cases hn : MisereOutcome (g + n)
  · exact False.elim ((MisereOutcome_eq_L_iff.mp hn).right hright_n)
  · simp
  · exact False.elim ((MisereOutcome_eq_P_iff.mp hn).left hright_n)
  · exact False.elim (hnotR_n hn)

def NTippingPoint.aux (g : GameForm) [h1 : Short g] :
    ∃ (n : ℕ), MisereOutcome (g + n) = .N ∨ MisereOutcome (g + (-n)) = .N := by
  by_cases h2 : MisereOutcome g = .R
  · have h3 : MisereOutcome (-g) = .L := by simp [h2]
    obtain ⟨n, hn⟩ := exists_add_nat_N_of_not_R (-g) (by simp [h3])
    refine ⟨n, Or.inr ?_⟩
    have h4 : (MisereOutcome (-g + n)).Conjugate = .N := by
      rw [hn]
      rfl
    simpa [outcome_conjugate_eq_outcome_neg, neg_add_rev, add_comm, add_left_comm, add_assoc] using h4
  · obtain ⟨n, hn⟩ := exists_add_nat_N_of_not_R g h2
    exact ⟨n, Or.inl hn⟩

noncomputable def NTippingPoint (g : GameForm) [Short g] : ℕ :=
  Nat.find (NTippingPoint.aux g)

@[simp]
theorem NTippingPoint.neg (g : GameForm) [Short g] : NTippingPoint (-g) = NTippingPoint g := by
  unfold NTippingPoint
  apply Nat.find_congr'
  intro n
  have hconjN : ∀ x : GameForm, MisereOutcome x = .N ↔ MisereOutcome (-x) = .N := by
    intro x
    constructor <;> intro hx
    · have : (MisereOutcome x).Conjugate = .N := by rw [hx]; rfl
      simpa [outcome_conjugate_eq_outcome_neg] using this
    · have : (MisereOutcome (-x)).Conjugate = .N := by rw [hx]; rfl
      simpa [outcome_conjugate_eq_outcome_neg] using this
  have h1 : MisereOutcome (g + n) = .N ↔ MisereOutcome (-g + (-n)) = .N := by
    simpa [neg_add_rev, add_comm, add_left_comm, add_assoc] using hconjN (g + n)
  have h2 : MisereOutcome (g + (-n)) = .N ↔ MisereOutcome (-g + n) = .N := by
    simpa [neg_add_rev, add_comm, add_left_comm, add_assoc] using hconjN (g + (-n))
  constructor <;> intro h
  · simpa [or_comm] using Or.imp h2.mpr h1.mpr h
  · simpa [or_comm] using Or.imp h1.mp h2.mp h

noncomputable def RTippingPoint (g : GameForm) [Short g] : ℕ :=
  Nat.find (RTippingPoint.aux g)

theorem RTippingPoint_iff (g : GameForm) [Short g] (n : ℕ) :
    (RTippingPoint g = n)
     ↔ ((MisereOutcome (g + n) = .R) ∧ ∀ (x : ℕ), MisereOutcome (g + x) = .R → n ≤ x) := by
  unfold RTippingPoint
  rw [Nat.find_eq_iff]
  constructor <;> intro ⟨h2, h3⟩ <;> apply And.intro h2 <;> intro x h4
  · exact Nat.le_of_not_lt fun h5 ↦ h3 x h5 h4
  · intro h5
    have h6 := h3 x h5
    omega

noncomputable def LTippingPoint (g : GameForm) [Short g] : ℕ :=
  Nat.find (LTippingPoint.aux g)

theorem LTippingPoint_iff (g : GameForm) [Short g] (n : ℕ) :
    (LTippingPoint g = n)
     ↔ ((MisereOutcome (g + (-n)) = .L) ∧ ∀ (x : ℕ), MisereOutcome (g + (-x)) = .L → n ≤ x) := by
  unfold LTippingPoint
  rw [Nat.find_eq_iff]
  constructor <;> intro ⟨h2, h3⟩ <;> apply And.intro h2 <;> intro x h4
  · exact Nat.le_of_not_lt fun h5 ↦ h3 x h5 h4
  · intro h5
    have h6 := h3 x h5
    omega
