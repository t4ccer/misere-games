module

public import CombinatorialGames.Misere.ShortUniverse.Comparison
public import CombinatorialGames.Misere.Universe.Comparison

universe u

variable {G : Type (u + 1)} [Form G]

open Form

public section

namespace Form

namespace ShortUniverse

theorem misere_ge_iff_maintenance_and_proviso {U : G → Prop} [ShortUniverse U]
    (g h : G) [h_g_short : Short g] [h_h_short : Short h] :
    g ≥m U h ↔ Maintenance U g h .right ∧ Maintenance U g h .left ∧
               Proviso U g h .right ∧ Proviso U h g .left := by
  constructor
  · intro h_ge
    exact Separation.ComparisonSet.misere_ge_imp_maintenance_and_proviso h_g_short h_h_short h_ge
  · intro ⟨h_mghr, h_mghl, h_pghr, h_pghl⟩
    exact Hereditary.MisereGe U h_mghr h_mghl h_pghr h_pghl

end ShortUniverse

namespace Universe

theorem misere_ge_iff_maintenance_and_proviso {U : G → Prop} [Universe U]
    (g h : G) :
    g ≥m U h ↔ Maintenance U g h .right ∧ Maintenance U g h .left ∧
               Proviso U g h .right ∧ Proviso U h g .left := by
  constructor
  · intro h_ge
    exact Separation.ComparisonSet.misere_ge_imp_maintenance_and_proviso trivial trivial h_ge
  · intro ⟨h_mghr, h_mghl, h_pghr, h_pghl⟩
    exact Hereditary.MisereGe U h_mghr h_mghl h_pghr h_pghl

end Universe

end Form
