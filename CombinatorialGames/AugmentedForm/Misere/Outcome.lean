module

public import CombinatorialGames.GameForm.Birthday
public import CombinatorialGames.AugmentedForm

public section

namespace AugmentedForm

open Form
open Form.Misere.Outcome

theorem WinsGoingFirst_of_hasTombstone {g : AugmentedForm} {p : Player} (h1 : hasTombstone p g)
    : WinsGoingFirst p g :=
  WinsGoingFirst_of_IsEndLike (IsEndLike_iff.mpr (Or.inl h1))

end AugmentedForm
