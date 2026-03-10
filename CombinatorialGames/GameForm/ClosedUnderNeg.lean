module

public import CombinatorialGames.GameForm

public section

namespace GameForm

class ClosedUnderNeg (A : GameForm → Prop) where
  neg_of {g : GameForm} (h1 : A g) : A (-g)

@[simp]
theorem ClosedUnderNeg.neg_iff {A : GameForm → Prop} [ClosedUnderNeg A] {g : GameForm}
    : A (-g) ↔ A g := by
  constructor
  · intro h1
    have h2 := ClosedUnderNeg.neg_of h1
    rwa [neg_neg] at h2
  · exact ClosedUnderNeg.neg_of
