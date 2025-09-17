/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import CombinatorialGames.GameForm
import CombinatorialGames.Form
import CombinatorialGames.Mathlib.NatOrdinal

/-!
# Birthdays of games

There are two related but distinct notions of a birthday within combinatorial game theory. One is
the birthday of an `GameForm`, which represents the "step" at which it is constructed. We define it
recursively as the least ordinal larger than the birthdays of its left and right options.

The birthday of an `GameForm` can be understood as representing the depth of its game tree.
-/

open NatOrdinal Order Set

universe u

namespace GameForm

open Form

/-- The birthday of an `IGame` is inductively defined as the least strict upper bound of the
birthdays of its options. It may be thought as the "step" in which a certain game is constructed. -/
noncomputable def birthday (x : GameForm.{u}) : NatOrdinal.{u} :=
  ⨆ y : {y // IsOption y x}, Order.succ (birthday y)
termination_by x
decreasing_by form_wf

theorem lt_birthday_iff' {x : GameForm} {o : NatOrdinal} : o < x.birthday ↔
    ∃ y, IsOption y x ∧ o ≤ y.birthday := by
  rw [birthday, NatOrdinal.lt_iSup_iff]
  simp only [succ_eq_add_one, lt_add_one_iff, Subtype.exists, exists_prop]

theorem birthday_le_iff' {x : GameForm} {o : NatOrdinal} : x.birthday ≤ o ↔
    ∀ y, IsOption y x → y.birthday < o := by
  simpa using lt_birthday_iff'.not

theorem lt_birthday_iff {x : GameForm} {o : NatOrdinal} : o < x.birthday ↔
    (∃ y ∈ xᴸ, o ≤ y.birthday) ∨ (∃ y ∈ xᴿ, o ≤ y.birthday) := by
  simp [lt_birthday_iff', isOption_iff_mem_union, or_and_right, exists_or, Form.moves]

theorem birthday_le_iff {x : GameForm} {o : NatOrdinal} : x.birthday ≤ o ↔
    (∀ y ∈ xᴸ, y.birthday < o) ∧ (∀ y ∈ xᴿ, y.birthday < o) := by
  simpa using lt_birthday_iff.not

theorem birthday_eq_max (x : GameForm) : birthday x =
    max (⨆ y : xᴸ, succ y.1.birthday) (⨆ y : xᴿ, succ y.1.birthday) := by
  apply eq_of_forall_lt_iff
  simp only [lt_birthday_iff, succ_eq_add_one, lt_sup_iff, NatOrdinal.lt_iSup_iff, lt_add_one_iff,
             Subtype.exists, exists_prop, implies_true]

@[aesop apply unsafe]
theorem birthday_lt_of_mem_moves {p : Player} {x y : GameForm} (hy : y ∈ x.moves p) :
    y.birthday < x.birthday :=
  lt_birthday_iff'.2 ⟨y, .of_mem_moves hy, le_rfl⟩

theorem birthday_lt_of_isOption {x y : GameForm} (hy : IsOption y x) : y.birthday < x.birthday :=
  lt_birthday_iff'.2 ⟨y, hy, le_rfl⟩

theorem birthday_lt_of_subposition {x y : GameForm} (hy : Subposition y x) :
    y.birthday < x.birthday := by
  cases hy with
  | single h => exact birthday_lt_of_isOption h
  | tail IH h => exact (birthday_lt_of_subposition IH).trans (birthday_lt_of_isOption h)
termination_by x
decreasing_by form_wf

theorem birthday_ofSets (s t : Set GameForm.{u}) [Small.{u} s] [Small.{u} t] :
    birthday !{s | t} = max (sSup (succ ∘ birthday '' s)) (sSup (succ ∘ birthday '' t)) := by
  rw [birthday_eq_max, leftMoves_ofSets, rightMoves_ofSets]
  simp [iSup, image_eq_range]

theorem birthday_ofSets_const (s : Set GameForm.{u}) [Small.{u} s] :
    birthday !{fun _ ↦ s} = sSup (succ ∘ birthday '' s) := by
  rw [ofSets_eq_ofSets_cases, birthday_ofSets, max_self]

@[simp]
theorem birthday_eq_zero {x : GameForm} : birthday x = 0 ↔ x = 0 := by
  rw [birthday, iSup_eq_zero_iff, GameForm.ext_iff]
  simp [isOption_iff_mem_union, forall_and, eq_empty_iff_forall_notMem, Form.moves]

@[simp]
theorem birthday_neg (x : GameForm) : (-x).birthday = x.birthday := by
  refine eq_of_forall_lt_iff fun y ↦ ?_
  rw [lt_birthday_iff, lt_birthday_iff, exists_moves_neg, exists_moves_neg, or_comm]
  congr! 3
  all_goals
    dsimp; rw [and_congr_right]
    intro h
    rw [birthday_neg]
termination_by x
decreasing_by form_wf

end GameForm
