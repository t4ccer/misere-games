/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

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

namespace Form

open Form

variable {G : Type (u + 1)} [g_form : Form G]

/-- The birthday of a form is inductively defined as the least strict upper bound of the
birthdays of its options. It may be thought as the "step" in which a certain game is constructed. -/
noncomputable def birthday (x : G) : NatOrdinal.{u + 1} :=
  ⨆ y : {y // IsOption y x}, Order.succ (birthday y)
termination_by x
decreasing_by form_wf

theorem lt_birthday_iff' {x : G} {o : NatOrdinal} : o < birthday x ↔
    ∃ y, IsOption y x ∧ o ≤ birthday y := by
  rw [birthday, NatOrdinal.lt_iSup_iff]
  simp only [succ_eq_add_one, lt_add_one_iff, Subtype.exists, exists_prop]

theorem birthday_le_iff' {x : G} {o : NatOrdinal} : birthday x ≤ o ↔
    ∀ y, IsOption y x → birthday y < o := by
  simpa using lt_birthday_iff'.not

theorem lt_birthday_iff {x : G} {o : NatOrdinal} : o < birthday x ↔
    (∃ y ∈ moves .left x, o ≤ birthday y) ∨ (∃ y ∈ moves .right x, o ≤ birthday y) := by
  simp [lt_birthday_iff', IsOption.iff_mem_union, or_and_right, exists_or]

theorem birthday_le_iff {x : G} {o : NatOrdinal} : birthday x ≤ o ↔
    (∀ y ∈ moves .left x, birthday y < o) ∧ (∀ y ∈ moves .right x, birthday y < o) := by
  simpa using lt_birthday_iff.not

theorem birthday_eq_max (x : G) : birthday x =
    max (⨆ y : moves .left x, succ (birthday y.1)) (⨆ y : moves .right x, succ (birthday y.1)) := by
  apply eq_of_forall_lt_iff
  simp only [lt_birthday_iff, succ_eq_add_one, lt_sup_iff, NatOrdinal.lt_iSup_iff, lt_add_one_iff,
             Subtype.exists, exists_prop, implies_true]

@[aesop apply unsafe]
theorem birthday_lt_of_mem_moves {p : Player} {x y : G} (hy : y ∈ moves p x) :
    birthday y < birthday x :=
  lt_birthday_iff'.2 ⟨y, .of_mem_moves hy, le_rfl⟩

theorem birthday_lt_of_isOption {x y : G} (hy : IsOption y x) : birthday y < birthday x :=
  lt_birthday_iff'.2 ⟨y, hy, le_rfl⟩

theorem birthday_lt_of_subposition {x y : G} (hy : Subposition y x) :
    birthday y < birthday x := by
  cases hy with
  | single h => exact birthday_lt_of_isOption h
  | tail IH h => exact (birthday_lt_of_subposition IH).trans (birthday_lt_of_isOption h)
termination_by x
decreasing_by form_wf

@[simp]
theorem birthday_neg (x : G) : birthday (-x) = birthday x := by
  refine eq_of_forall_lt_iff fun y ↦ ?_
  rw [lt_birthday_iff, lt_birthday_iff]
  rw [exists_moves_neg, exists_moves_neg, or_comm]
  congr! 3
  all_goals
    dsimp; rw [and_congr_right]
    intro h
    rw [birthday_neg]
termination_by x
decreasing_by form_wf

end Form
