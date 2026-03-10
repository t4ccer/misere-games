/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Form.Misere.Outcome
public import CombinatorialGames.GameForm.Birthday

public noncomputable section

namespace GameForm.Misere.Outcome

open Form
open Form.Misere.Outcome
open MisereForm

universe u

private def WinsGoingFirst' (p : Player) (g : GameForm) : Prop :=
  Form.IsEnd p g ∨ (∃ g', ∃ (_ : g' ∈ Form.moves p g), ¬WinsGoingFirst' (-p) g')
termination_by g
decreasing_by form_wf

private theorem End_WinsGoingFirst' {g : GameForm} {p : Player} (h1 : IsEnd p g)
    : WinsGoingFirst' p g := by
  rw [WinsGoingFirst']
  exact Or.inl h1

private theorem WinsGoingFirst_neg_iff' (g : GameForm) (p : Player) :
    (WinsGoingFirst' p (-g)) ↔ (WinsGoingFirst' (-p) g) := by
  constructor
    <;> intro h1
    <;> rw [WinsGoingFirst'] at h1
    <;> apply Or.elim h1
    <;> intro h1
  · exact End_WinsGoingFirst' (IsEnd_neg_iff_neg.mp h1)
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [WinsGoingFirst', neg_neg]
    simp only [exists_prop]
    apply Or.inr
    use -gp
    simp only [Form.moves_neg, Set.mem_neg] at h1
    exact And.intro h1 ((WinsGoingFirst_neg_iff' gp p).not.mpr h2)
  · exact End_WinsGoingFirst' (IsEnd_neg_iff_neg.mpr h1)
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [WinsGoingFirst']
    apply Or.inr
    use -gp
    simp only [Form.moves_neg, Set.mem_neg, neg_neg, exists_prop]
    apply And.intro h1
    have h3 := (WinsGoingFirst_neg_iff' (-gp) p).not.mp
    rw [neg_neg] at h2 h3
    exact h3 h2
termination_by Form.birthday g
decreasing_by all_goals gameform_birthday

private theorem WinsGoingFirst_iff' (g : GameForm) (p : Player)
    : WinsGoingFirst' p g ↔ IsEnd p g ∨ (∃ g' ∈ moves p g, ¬WinsGoingFirst' (-p) g') := by
  rw [WinsGoingFirst']
  simp only [exists_prop]

@[no_expose] instance : MisereForm GameForm where
  WinsGoingFirst := WinsGoingFirst'
  WinsGoingFirst_neg_iff' := WinsGoingFirst_neg_iff'
  WinsGoingFirst_iff p g := by simp only [WinsGoingFirst_iff' p g, IsEndLike_iff]

@[simp]
theorem one_MisereOutcome_R : MisereOutcome (1 : GameForm) = .R := by
  simp only [MisereOutcome_eq_R_iff]
  constructor
  · refine WinsGoingFirst_of_IsEnd ?_
    simp only [IsEnd_def, GameForm.one_def, GameForm.moves_ofSets, Player.cases]
  · rw [not_WinsGoingFirst]
    simp [IsEnd_def]

@[simp]
theorem pos_nat_MisereOutcome_R {n : ℕ} (h1 : n > 0) : MisereOutcome (n : GameForm) = .R := by
  induction n, h1 using Nat.le_induction with
  | base => simp
  | succ k h2 ih =>
    rw [Nat.cast_add, Nat.cast_one, MisereOutcome_eq_R_iff]
    constructor
    · exact WinsGoingFirst_of_IsEnd (nat_IsEnd_right (k + 1))
    · rw [not_WinsGoingFirst]
      simp [IsEnd_def]

@[simp]
theorem pos_int_MisereOutcome_R {n : ℤ} (h1 : n > 0) : MisereOutcome (n : GameForm) = .R := by
  rw [<-Int.toNat_of_nonneg (Int.le_of_lt h1)]
  exact pos_nat_MisereOutcome_R (Int.pos_iff_toNat_pos.mp h1)

@[simp]
theorem neg_int_MisereOutcome_L {n : ℤ} (h1 : n < 0) : MisereOutcome (n : GameForm) = .L := by
  have h2 := pos_int_MisereOutcome_R.{u_1} (Int.neg_pos.mpr h1)
  rwa [intCast_neg, neg_MisereOutcome_R_iff] at h2

@[simp]
theorem zero_int_MisereOutcome_N {n : ℤ} (h1 : n = 0) : MisereOutcome (n : GameForm) = .N := by
  rw [h1, intCast_ofNat, Nat.cast_zero, zero_MisereOutcome_N]

end GameForm.Misere.Outcome
