/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.GameForm

universe u

public section

-- TODO: Rename: It's a class for game positions, "ruleset" sounds like the set of all game positions
class Ruleset (R : Type u) where
  toGameForm : R → GameForm
  has_zero : ∃ r, toGameForm r = 0
  moves_toGameForm (p : Player) (r : R) :
      ∀ g' ∈ Form.moves p (toGameForm r), ∃ r', toGameForm r' = g'
