import CombinatorialGames.GameForm.Birthday
import CombinatorialGames.AugmentedForm

namespace AugmentedForm

open Form
open MisereForm

private def WinsGoingFirst' (p : Player) (g : AugmentedForm) : Prop :=
  EndLike p g ∨ (∃ g', ∃ (_ : g' ∈ Form.moves p g), ¬WinsGoingFirst' (-p) g')
termination_by g
decreasing_by form_wf

private theorem hasTombstone_WinsGoingFirst' {g : AugmentedForm} {p : Player} (h1 : hasTombstone p g)
    : WinsGoingFirst' p g := by
  rw [WinsGoingFirst', EndLike]
  exact Or.inl (Or.inl h1)

private theorem EndLike_WinsGoingFirst' {g : AugmentedForm} {p : Player} (h1 : EndLike p g)
    : WinsGoingFirst' p g := by
  rw [WinsGoingFirst']
  exact Or.inl h1

private theorem End_WinsGoingFirst' {g : AugmentedForm} {p : Player} (h1 : IsEnd p g)
    : WinsGoingFirst' p g := by
  apply EndLike_WinsGoingFirst'
  exact IsEnd.EndLike h1

private theorem WinsGoingFirst_neg_iff' (g : AugmentedForm) (p : Player) :
    (WinsGoingFirst' p (-g)) ↔ (WinsGoingFirst' (-p) g) := by
  constructor
    <;> intro h1
    <;> rw [WinsGoingFirst'] at h1
    <;> apply Or.elim h1
    <;> intro h1
  · apply Or.elim h1 <;> intro h1
    · exact hasTombstone_WinsGoingFirst' (hasTombstone_neg_iff.mp h1)
    · exact End_WinsGoingFirst' (IsEnd_neg_iff_neg.mp h1)
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [WinsGoingFirst', neg_neg]
    simp only [exists_prop]
    apply Or.inr
    use -gp
    simp [moves_neg] at h1
    exact And.intro h1 ((WinsGoingFirst_neg_iff' gp p).not.mpr h2)
  · apply Or.elim h1 <;> intro h1
    · exact hasTombstone_WinsGoingFirst' (hasTombstone_neg_iff.mpr h1)
    · exact End_WinsGoingFirst' (IsEnd_neg_iff_neg.mpr h1)
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
  WinsGoingFirst_neg_iff' := WinsGoingFirst_neg_iff'
  WinsGoingFirst_of_IsEnd' g p h1 := by
    unfold WinsGoingFirst'
    apply Or.inl
    unfold EndLike
    exact Or.inr h1

private theorem WinsGoingFirst_def {g : AugmentedForm} {p : Player}
    : WinsGoingFirst p g ↔ WinsGoingFirst' p g := by
  simp only [WinsGoingFirst]

theorem WinsGoingFirst_iff {g : AugmentedForm} {p : Player}
    : WinsGoingFirst p g ↔ (EndLike p g) ∨ (∃ g' ∈ Form.moves p g, ¬WinsGoingFirst (-p) g') := by
  nth_rw 1 [WinsGoingFirst, instMisereForm]
  dsimp only [instForm.eq_1]
  unfold WinsGoingFirst'
  simp only [exists_prop, <-WinsGoingFirst_def]

theorem WinsGoingFirst_of_hasTombstone {g : AugmentedForm} {p : Player} (h1 : hasTombstone p g)
    : WinsGoingFirst p g := hasTombstone_WinsGoingFirst' h1

theorem WinsGoingFirst_of_EndLike {g : AugmentedForm} {p : Player} (h1 : EndLike p g)
    : WinsGoingFirst p g := EndLike_WinsGoingFirst' h1

theorem WinsGoingFirst_of_End {g : AugmentedForm} {p : Player} (h1 : IsEnd p g)
    : WinsGoingFirst p g := End_WinsGoingFirst' h1

theorem WinsGoingFirst_of_moves {g : AugmentedForm} {p : Player}
    (h1 : ∃ g' ∈ moves p g, ¬WinsGoingFirst (-p) g')
    : WinsGoingFirst p g := by
  simp only [WinsGoingFirst]
  unfold WinsGoingFirst'
  apply Or.inr
  exact bex_def.mpr h1

theorem not_WinsGoingFirst {g : AugmentedForm} {p : Player}
    : ¬WinsGoingFirst p g ↔ (¬EndLike p g ∧ (∀ g' ∈ moves p g, WinsGoingFirst (-p) g')) := by
  rw [WinsGoingFirst_iff]
  simp only [not_or, not_EndLike, not_exists, not_and, not_not]

end AugmentedForm
