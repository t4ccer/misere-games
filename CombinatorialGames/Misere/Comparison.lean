/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import CombinatorialGames.Misere.ShortUniverse.Comparison
public import CombinatorialGames.Misere.Universe.Comparison

universe u

variable {G : Type (u + 1)} [Form G]

open Form

public section

namespace Form

namespace Separation.ComparisonSet

theorem misereGE_iff_maintenance_proviso {A : G → Prop} [ComparisonSet A] [Hereditary A]
    {g h : G} (h_g : IsAmbient A g) (h_h : IsAmbient A h) :
    g ≥m A h ↔ Maintenance A g h .right ∧ Maintenance A g h .left ∧
               Proviso A g h .right ∧ Proviso A h g .left := by
  constructor
  · intro h_ge
    apply maintenance_proviso_of_misereGE
    · exact h_g
    · exact h_h
    · exact h_ge
  · intro ⟨h_mghr, h_mghl, h_pghr, h_pghl⟩
    exact Hereditary.misereGE_of_maintenance_proviso A h_mghr h_mghl h_pghr h_pghl

end Separation.ComparisonSet

end Form
