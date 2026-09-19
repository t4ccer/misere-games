/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Player

/-!
# Hackenbush colours

Edges in Hackenbush are bLue (Left's), Red (Right's) or green (either
player's).
-/

public section

namespace Hackenbush

inductive Color where
  | blue : Color
  | red : Color
  | green : Color
deriving DecidableEq

namespace Color

/--
The colour of player `p`'s edges.
-/
def ofPlayer : Player → Color
  | .left => blue
  | .right => red

@[simp] theorem ofPlayer_left : ofPlayer .left = blue := by rw [ofPlayer]
@[simp] theorem ofPlayer_right : ofPlayer .right = red := by rw [ofPlayer]

@[simp]
theorem ofPlayer_inj {p q : Player} : ofPlayer p = ofPlayer q ↔ p = q := by
  cases p <;> cases q <;> simp

@[simp]
theorem ofPlayer_ne_green (p : Player) : ofPlayer p ≠ green := by
  cases p <;> simp

@[simp]
theorem green_ne_ofPlayer (p : Player) : green ≠ ofPlayer p :=
  (ofPlayer_ne_green p).symm

theorem ofPlayer_ne_ofPlayer_neg (p : Player) : ofPlayer p ≠ ofPlayer (-p) := by
  cases p <;> simp

/--
Every colour may be cut by some player.
-/
theorem exists_ne_ofPlayer_neg (c : Color) : ∃ p, c ≠ ofPlayer (-p) := by
  cases c
  · exact ⟨.left, by simp⟩
  · exact ⟨.right, by simp⟩
  · exact ⟨.left, by simp⟩

theorem eq_ofPlayer_neg_of_ne {c : Color} {p : Player} (h_green : c ≠ green)
    (h_ne : c ≠ ofPlayer p) : c = ofPlayer (-p) := by
  cases c <;> cases p <;> simp_all

theorem exists_eq_ofPlayer {c : Color} (h_green : c ≠ green) : ∃ p, c = ofPlayer p := by
  cases c
  · exact ⟨.left, rfl⟩
  · exact ⟨.right, rfl⟩
  · exact absurd rfl h_green

end Color

end Hackenbush
