/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.GameForm
public import CombinatorialGames.Misere.Hereditary

universe u

public section

open Form

class Ruleset (R : Type u) where
  toGameForm : R → GameForm
  moves_toGameForm (p : Player) (r : R) :
      ∀ g' ∈ Form.moves p (toGameForm r), ∃ r', toGameForm r' = g'

/--
Set of `GameForm`s created by the positions in rulset `R`
-/
def Ruleset.Forms (R : Type u) [Ruleset R] (g : GameForm) : Prop
  := ∃ (r : R), g = Ruleset.toGameForm r

theorem Ruleset.Forms.exists {R : Type u} [Ruleset R] {g : GameForm} (h_g : Ruleset.Forms R g) :
    ∃ (r : R), g = Ruleset.toGameForm r := by
  unfold Forms at h_g
  exact h_g

theorem Ruleset.Forms.position_mem {R : Type u} [Ruleset R] (r : R) :
    Ruleset.Forms R (Ruleset.toGameForm r) := by
  unfold Forms
  use r

instance {R : Type u} [Ruleset R] : Hereditary (Ruleset.Forms R) where
  has_option h_g h_g' := by
    simp [isOption_iff_mem_union] at h_g'
    obtain ⟨r, h_r⟩ := Ruleset.Forms.exists h_g
    obtain h_mem | h_mem := h_g'
    · rw [h_r] at h_mem
      have ⟨r', h1⟩ := Ruleset.moves_toGameForm .left r _ h_mem
      rw [<-h1]
      exact Ruleset.Forms.position_mem r'
    · rw [h_r] at h_mem
      have ⟨r', h1⟩ := Ruleset.moves_toGameForm .right r _ h_mem
      rw [<-h1]
      exact Ruleset.Forms.position_mem r'
