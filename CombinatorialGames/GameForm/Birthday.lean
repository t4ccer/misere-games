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
  rw [ofSets_eq_ofSets_cases, birthday_ofSets, max_self]

@[simp]
theorem birthday_eq_zero {x : GameForm} : birthday x = 0 ↔ x = 0 := by
  rw [birthday, iSup_eq_zero_iff, GameForm.ext_iff]
  simp only [succ_eq_add_one, add_one_ne_zero, Subtype.forall, IsOption.iff_mem_union, mem_union,
             imp_false, not_or, forall_and, moves_zero, eq_empty_iff_forall_notMem, Player.forall]

end GameForm
