/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import CombinatorialGames.Misere.Separation
public import CombinatorialGames.Misere.Universe

universe u

variable {G : Type (u + 1)} [Form G]

open Form

public section

namespace Form

namespace LongUniverse

variable {U : G → Prop} [LongUniverse U]

instance : Separation.ComparisonSet.UniverseAdapter (fun _ => True) U where
  toUniverse := inferInstance
  isAmbient_hereditary := { has_option _ _ := trivial }
  isAmbient_closed_neg := { neg_of _ := trivial }
  isAmbient_adjoint _ := by
    trivial
  isAmbient_rightSeparatorCandidate _ _ := by
    trivial
  isAmbient_downlinkWitness _ _ _ _ := by
    trivial

end LongUniverse

end Form
