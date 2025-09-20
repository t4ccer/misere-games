import CombinatorialGames.GameForm.Misere.Outcome

namespace Form

universe u

variable {G : Type u} [g_form : Form G]

open Form

def IsDeadEnd (p : Player) (g : G) : Prop :=
  IsEnd p g ∧ (∀ gp ∈ moves (-p) g, IsDeadEnd p gp)
termination_by g
decreasing_by form_wf

def IsDeadEnd_IsEnd {g : G} {p : Player} (h1 : IsDeadEnd p g) : IsEnd p g := by
  unfold IsDeadEnd at h1
  exact h1.left

def IsDeadEnd_moves {g : G} {p : Player} (h1 : IsDeadEnd p g) :
    ∀ gp ∈ moves (-p) g, IsDeadEnd p gp := by
  unfold IsDeadEnd at h1
  exact h1.right

theorem IsDeadEnd.add {g h : G} {p : Player} (h1 : IsDeadEnd p g) (h2 : IsDeadEnd p h) :
    IsDeadEnd p (g + h) := by
  unfold IsDeadEnd
  simp only [moves_add, Set.mem_union, Set.mem_image]
  apply And.intro (IsEnd.add_iff.mpr ⟨IsDeadEnd_IsEnd h1, IsDeadEnd_IsEnd h2⟩)
  intro gp h3
  apply Or.elim h3 <;> intro ⟨gpp, h3, h4⟩ <;> rw [<-h4]
  · exact IsDeadEnd.add (IsDeadEnd_moves h1 gpp h3) h2
  · exact IsDeadEnd.add h1 (IsDeadEnd_moves h2 gpp h3)
termination_by (g, h)
decreasing_by all_goals form_wf

def IsDeadEnding (g : G) : Prop :=
  (∀ p, IsEnd p g → IsDeadEnd p g) ∧ (∀ p, ∀gp ∈ moves p g, IsDeadEnding gp)
termination_by g
decreasing_by form_wf

@[simp]
theorem IsDeadEnding.IsDeadEnd {g : G} {p : Player} (h1 : IsDeadEnding g) (h2 : IsEnd p g) :
    IsDeadEnd p g := by
  unfold IsDeadEnding at h1
  exact h1.left p h2

@[simp]
theorem IsDeadEnding.moves {g h : G} {p : Player} (h1 : IsDeadEnding g) (h2 : h ∈ moves p g) :
    IsDeadEnding h := by
  unfold IsDeadEnding at h1
  exact h1.right p h h2

end Form

namespace GameForm

open GameForm.Misere.Outcome
open Form
open Form.Misere.Outcome

private theorem lemma3.aux {g : GameForm} {p : Player} (h1 : g ≠ 0) (h2 : IsDeadEnd p g) :
    MisereForm.MisereOutcome g = Outcome.ofPlayer p := by
  rw [MisereOutcome_eq_player_iff]
  apply And.intro (End_WinsGoingFirst (IsDeadEnd_IsEnd h2))
  rw [WinsGoingFirst_def]
  simp only [exists_prop, not_or, not_exists, not_and, not_not, neg_neg]
  apply And.intro (zero_not_both_end h1 (IsDeadEnd_IsEnd h2))
  intro gr h4
  exact End_WinsGoingFirst (IsDeadEnd_IsEnd (IsDeadEnd_moves h2 gr h4))

theorem lemma3_L (g : GameForm) (h1 : g ≠ 0) (h2 : IsDeadEnd .left g) :
    MisereForm.MisereOutcome g = .L := lemma3.aux h1 h2

theorem lemma3_R (g : GameForm) (h1 : g ≠ 0) (h2 : IsDeadEnd .right g) :
    MisereForm.MisereOutcome g = .R := lemma3.aux h1 h2

@[simp]
theorem IsDeadEnding.add {g h : GameForm} (h1 : IsDeadEnding g) (h2 : IsDeadEnding h) :
    IsDeadEnding (g + h) := by
  unfold IsDeadEnding
  simp only [moves_add, Set.mem_union, Set.mem_image, Form.moves]
  constructor <;> intro p
  · intro h3
    have ⟨h4, h5⟩ := IsEnd.add_iff.mp h3
    exact IsDeadEnd.add (IsDeadEnding.IsDeadEnd h1 h4) (IsDeadEnding.IsDeadEnd h2 h5)
  · intro gp h3
    apply Or.elim h3 <;> intro ⟨g', h3, h4⟩ <;> rw [<-h4]
    · exact IsDeadEnding.add (IsDeadEnding.moves h1 h3) h2
    · exact IsDeadEnding.add h1 (IsDeadEnding.moves h2 h3)
termination_by (g, h)
decreasing_by all_goals form_wf

end GameForm
