import CombinatorialGames.GameForm.Birthday
import CombinatorialGames.AugmentedForm

namespace AugmentedForm

open Form

def WinsGoingFirst' (p : Player) (g : AugmentedForm) : Prop :=
  EndLike g p ∨ (∃ g', ∃ (_ : g' ∈ Form.moves p g), ¬WinsGoingFirst' (-p) g')
termination_by g
decreasing_by form_wf

theorem hasTombstone_WinsGoingFirst {g : AugmentedForm} {p : Player} (h1 : hasTombstone p g)
    : WinsGoingFirst' p g := by
  rw [WinsGoingFirst', EndLike]
  exact Or.inl (Or.inl h1)

theorem End_WinsGoingFirst {g : AugmentedForm} {p : Player} (h1 : IsEnd p g)
    : WinsGoingFirst' p g := by
  rw [WinsGoingFirst']
  exact Or.inl (Or.inr h1)

private theorem WinsGoingFirst_neg_iff' (g : AugmentedForm) (p : Player) :
    (WinsGoingFirst' p (-g)) ↔ (WinsGoingFirst' (-p) g) := by
  constructor
    <;> intro h1
    <;> rw [WinsGoingFirst'] at h1
    <;> apply Or.elim h1
    <;> intro h1
  · apply Or.elim h1 <;> intro h1
    · exact hasTombstone_WinsGoingFirst (hasTombstone_neg_iff.mp h1)
    · exact End_WinsGoingFirst (IsEnd_neg_iff_neg.mp h1)
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [WinsGoingFirst', neg_neg]
    simp only [exists_prop]
    apply Or.inr
    use -gp
    simp [moves_neg] at h1
    exact And.intro h1 ((WinsGoingFirst_neg_iff' gp p).not.mpr h2)
  · apply Or.elim h1 <;> intro h1
    · exact hasTombstone_WinsGoingFirst (hasTombstone_neg_iff.mpr h1)
    · exact End_WinsGoingFirst (IsEnd_neg_iff_neg.mpr h1)
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [WinsGoingFirst']
    apply Or.inr
    use -gp
    simp only [Form.moves_neg, Set.mem_neg, neg_neg, exists_prop]
    apply And.intro h1
    have h3 := (WinsGoingFirst_neg_iff' (-gp) p).not.mp
    rw [neg_neg] at h2 h3
    exact h3 h2
termination_by Form.birthday g
decreasing_by
  · rw [<-Form.birthday_neg g]
    exact Form.birthday_lt_of_mem_moves h1
  · rw [Form.birthday_neg gp]
    exact Form.birthday_lt_of_mem_moves h1

noncomputable instance : MisereForm AugmentedForm where
  WinsGoingFirst := WinsGoingFirst'
  WinsGoingFirst_neg_iff := WinsGoingFirst_neg_iff'

end AugmentedForm
