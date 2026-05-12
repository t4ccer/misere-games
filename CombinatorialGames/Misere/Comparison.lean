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
    (g h : G) [Short g] [Short h] :
    g ≥m U h ↔ Maintenance U g h .right ∧ Maintenance U g h .left ∧
               Proviso U g h .right ∧ Proviso U h g .left := by
  constructor
  · exact misere_ge_imp_maintenance_and_proviso g h
  · intro hmp
    exact Hereditary.MisereGe U hmp.1 hmp.2.1 hmp.2.2.1 hmp.2.2.2

end ShortUniverse

namespace Universe

theorem misere_ge_iff_maintenance_and_proviso {U : G → Prop} [Universe U]
    (g h : G) :
    g ≥m U h ↔ Maintenance U g h .right ∧ Maintenance U g h .left ∧
               Proviso U g h .right ∧ Proviso U h g .left := by
  constructor
  · exact misere_ge_imp_maintenance_and_proviso g h
  · intro hmp
    exact Hereditary.MisereGe U hmp.1 hmp.2.1 hmp.2.2.1 hmp.2.2.2

end Universe

end Form
