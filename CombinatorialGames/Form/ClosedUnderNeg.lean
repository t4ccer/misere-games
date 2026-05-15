/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Form

public section

namespace Form

universe u

variable {G : Type (u + 1)} [Form G]

class ClosedUnderNeg (A : G → Prop) where
  neg_of {g : G} (h1 : A g) : A (-g)

instance : ClosedUnderNeg (fun _ => True) (G := G) where
  neg_of _ := trivial

@[simp, nolint simpVarHead] -- It does fire, despite what linter comment says
theorem ClosedUnderNeg.neg_iff {A : G → Prop} [ClosedUnderNeg A] {g : G}
    : A (-g) ↔ A g := by
  constructor
  · intro h1
    have h2 := ClosedUnderNeg.neg_of h1
    rwa [neg_neg (G := G)] at h2
  · exact ClosedUnderNeg.neg_of
