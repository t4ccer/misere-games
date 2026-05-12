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
open Form.Separation.ComparisonSet

public section

namespace Form

namespace ShortUniverse

theorem misereGE_iff_maintenance_proviso {U : G → Prop} [ShortUniverse U]
    {g h : G} (h_g : IsShort g) (h_h : IsShort h) :
    g ≥m U h ↔ Maintenance U g h .right ∧ Maintenance U g h .left ∧
               Proviso U g h .right ∧ Proviso U h g .left := by
  constructor
  · intro h_ge
    exact maintenance_proviso_of_misereGE h_g h_h h_ge
  · intro ⟨h_mghr, h_mghl, h_pghr, h_pghl⟩
    exact Hereditary.misereGE_of_maintenance_proviso U h_mghr h_mghl h_pghr h_pghl

end ShortUniverse

namespace Universe

theorem misereGE_iff_maintenance_proviso {U : G → Prop} [Universe U]
    (g h : G) :
    g ≥m U h ↔ Maintenance U g h .right ∧ Maintenance U g h .left ∧
               Proviso U g h .right ∧ Proviso U h g .left := by
  constructor
  · intro h_ge
    exact maintenance_proviso_of_misereGE trivial trivial h_ge
  · intro ⟨h_mghr, h_mghl, h_pghr, h_pghl⟩
    exact Hereditary.misereGE_of_maintenance_proviso U h_mghr h_mghl h_pghr h_pghl

end Universe

end Form
