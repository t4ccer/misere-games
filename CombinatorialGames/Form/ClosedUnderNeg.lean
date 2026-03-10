module

public import CombinatorialGames.Form

public section

namespace Form

universe u

variable {G : Type (u + 1)} [Form G]

class ClosedUnderNeg (A : G → Prop) where
  neg_of {g : G} (h1 : A g) : A (-g)

@[simp]
theorem ClosedUnderNeg.neg_iff {A : G → Prop} [ClosedUnderNeg A] {g : G}
    : A (-g) ↔ A g := by
  constructor
  · intro h1
    have h2 := ClosedUnderNeg.neg_of h1
    rwa [neg_neg (G := G)] at h2
  · exact ClosedUnderNeg.neg_of
