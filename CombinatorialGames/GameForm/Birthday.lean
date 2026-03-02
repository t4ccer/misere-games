/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import CombinatorialGames.Form.Birthday
import CombinatorialGames.GameForm
import CombinatorialGames.Mathlib.NatOrdinal

open NatOrdinal Order Set

universe u

namespace GameForm

open Form

theorem birthday_ofSets (s t : Set GameForm.{u}) [Small.{u} s] [Small.{u} t] :
    birthday !{s | t} = max (sSup (succ ∘ birthday '' s)) (sSup (succ ∘ birthday '' t)) := by
  rw [birthday_eq_max]
  rw [leftMoves_ofSets, rightMoves_ofSets]
  simp only [iSup, succ_eq_add_one, Function.comp_apply, image_eq_range]

theorem birthday_ofSets_const (s : Set GameForm.{u}) [Small.{u} s] :
    birthday !{fun _ ↦ s} = sSup (succ ∘ birthday '' s) := by
  rw [ofSets_eq_ofSets_cases, birthday_ofSets]
  exact max_eq_left le_rfl

@[simp]
theorem birthday_eq_zero {x : GameForm} : birthday x = 0 ↔ x = 0 := by
  rw [birthday, iSup_eq_zero_iff, GameForm.ext_iff]
  simp only [succ_eq_add_one, add_one_ne_zero, Subtype.forall, IsOption.iff_mem_union, mem_union,
             imp_false, not_or, forall_and, moves_zero, eq_empty_iff_forall_notMem, Player.forall]

noncomputable def birthdayFinset : ℕ → Finset GameForm.{u}
  | 0 => {0}
  | n + 1 => ((birthdayFinset n).powerset ×ˢ (birthdayFinset n).powerset).map
    ⟨fun a => !{a.1 | a.2}, fun a b hab => by aesop⟩

theorem mem_birthdayFinset_succ {x : GameForm} {n : ℕ} : x ∈ birthdayFinset (n + 1) ↔
    ∃ l r, (l ⊆ birthdayFinset n ∧ r ⊆ birthdayFinset n) ∧ !{l | r} = x := by
  simp [birthdayFinset]

@[simp]
theorem birthdayFinset_zero : birthdayFinset 0 = {0} := rfl

@[simp]
theorem mem_birthdayFinset {x : GameForm} {n : ℕ} : x ∈ birthdayFinset n ↔ birthday x ≤ n := by
  induction n generalizing x with
  | zero =>
    simp [birthdayFinset_zero, birthday_eq_zero]
  | succ n IH =>
    simp_rw [mem_birthdayFinset_succ, birthday_le_iff, Finset.subset_iff, Nat.cast_add_one,
      ← succ_eq_add_one, lt_succ_iff, IH]
    constructor
    · aesop
    · rintro ⟨hl, hr⟩
      have hxl : xᴸ ⊆ birthdayFinset n := fun y hy => (IH (x := y)).2 (hl y hy)
      have hxr : xᴿ ⊆ birthdayFinset n := fun y hy => (IH (x := y)).2 (hr y hy)
      classical
      have := Set.fintypeSubset _ hxl
      have := Set.fintypeSubset _ hxr
      use xᴸ.toFinset, xᴿ.toFinset
      simp_all only [mem_toFinset, implies_true, and_self, coe_toFinset, ofSets_leftMoves_rightMoves]


end GameForm
