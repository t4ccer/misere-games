/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Tristan Figueroa Reid
-/

import CombinatorialGames.Form.Short

/-!
# Special games

This file defines some simple yet notable combinatorial games:

* `⋆ = {0 | 0}`
* `½ = {0 | 1}`
* `↑ = {0 | ⋆}`
* `↓ = {⋆ | 0}`
-/

universe u

namespace GameForm

open Form (Short short_def)

/-! ### Star -/

/-- The game `⋆ = {0 | 0}`, which is fuzzy with zero. -/
def star : GameForm :=
  !{fun _ ↦ {0}}

@[inherit_doc] notation "⋆" => star
recommended_spelling "star" for "⋆" in [«term⋆»]

@[simp] theorem leftMoves_star : ⋆ᴸ = {0} := moves_ofSets ..
@[simp] theorem rightMoves_star : ⋆ᴿ = {0} := moves_ofSets ..

-- TODO: remove the above theorems
@[simp] theorem moves_star (p : Player) : moves p ⋆ = {0} := moves_ofSets ..

@[simp] theorem neg_star : -⋆ = ⋆ := by simp [star]

@[simp] instance : Short ⋆ := by
  rw [star, Form.short_def]; simp [Form.moves]

/-! ### Half -/

/-- The game `½ = {0 | 1}`, which we prove satisfies `½ + ½ = 1`. -/
def half : GameForm :=
  !{{0} | {1}}

@[inherit_doc] notation "½" => half
recommended_spelling "half" for "½" in [«term½»]

@[simp] theorem leftMoves_half : ½ᴸ = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_half : ½ᴿ = {1} := rightMoves_ofSets ..

instance : Short ½ := by
  rw [half, Form.short_def]; simp [Form.moves]

/-! ### Up and down -/

/-- The game `↑ = {0 | ⋆}`. -/
def up : GameForm :=
  !{{0} | {⋆}}

@[inherit_doc] notation "↑" => up
recommended_spelling "up" for "↑" in [«term↑»]

@[simp] theorem leftMoves_up : ↑ᴸ = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_up : ↑ᴿ = {⋆} := rightMoves_ofSets ..

instance : Short ↑ := by
  rw [up, Form.short_def]; simp [Form.moves]

/-- The game `↓ = {⋆ | 0}`. -/
def down : GameForm :=
  !{{⋆} | {0}}

@[inherit_doc] notation "↓" => down
recommended_spelling "down" for "↓" in [«term↓»]

@[simp] theorem leftMoves_down : ↓ᴸ = {⋆} := leftMoves_ofSets ..
@[simp] theorem rightMoves_down : ↓ᴿ = {0} := rightMoves_ofSets ..

@[simp] theorem neg_down : -↓ = ↑ := by simp [up, down]
@[simp] theorem neg_up : -↑ = ↓ := by simp [up, down]

instance : Short ↓ := by
  rw [down, Form.short_def]; simp [Form.moves]

/-! ### Tiny and miny -/

/-- A tiny game `⧾x` is defined as `{0 | {0 | -x}}`, and is amongst the smallest of the
infinitesimals. -/
def tiny (x : GameForm) : GameForm :=
  !{{0} | {!{{0} | {-x}}}}

@[inherit_doc] prefix:75 "⧾" => tiny
recommended_spelling "tiny" for "⧾" in [«term⧾_»]

@[simp]
theorem leftMoves_tiny (x : GameForm) : (⧾x)ᴸ = {0} :=
  leftMoves_ofSets ..

@[simp]
theorem rightMoves_tiny (x : GameForm) : (⧾x)ᴿ = {!{{0} | {-x}}} :=
  rightMoves_ofSets ..

instance (x : GameForm) [Short x] : Short (⧾x) := by
  have : Short (!{{0} | {-x}}) := by rw [Form.short_def]; simp [Form.moves]; infer_instance
  rw [tiny, Form.short_def]; simp [Form.moves, this]

/-- A miny game `⧿x` is defined as `{{x | 0} | 0}`. -/
def miny (x : GameForm) : GameForm :=
  !{{!{{x} | {0}}} | {0}}

@[inherit_doc] prefix:75 "⧿" => miny
recommended_spelling "miny" for "⧿" in [«term⧿_»]

@[simp]
theorem leftMoves_miny (x : GameForm) : (⧿x)ᴸ = {!{{x} | {0}}} :=
  leftMoves_ofSets ..

@[simp]
theorem rightMoves_miny (x : GameForm) : (⧿x)ᴿ = {0} :=
  rightMoves_ofSets ..

@[simp]
theorem neg_tiny (x : GameForm) : -(⧾x) = ⧿x := by
  simp [miny, tiny]

@[simp]
theorem neg_miny (x : GameForm) : -(⧿x) = ⧾x := by
  simp [miny, tiny]

instance (x : GameForm) [Short x] : Short (⧿x) := by
  rw [← neg_tiny]; infer_instance

/-! ### Switches -/

/-- A **switch** `±x` is defined as `{x | -x}`: switches are their own confusion interval! -/
def switch (x : GameForm) : GameForm :=
  !{{x} | {-x}}

@[inherit_doc] prefix:75 "±" => switch
recommended_spelling "switch" for "±" in [«term±_»]

@[simp]
theorem leftMoves_switch (x : GameForm) : (±x)ᴸ = {x} :=
  leftMoves_ofSets ..

@[simp]
theorem rightMoves_switch (x : GameForm) : (±x)ᴿ = {-x} :=
  rightMoves_ofSets ..

@[simp]
theorem neg_switch (x : GameForm) : -±x = ±x := by
  rw [switch, neg_ofSets]
  simp [Set.neg_singleton]

@[simp]
theorem switch_zero : ±0 = ⋆ := by
  ext p; cases p <;> simp

end GameForm
