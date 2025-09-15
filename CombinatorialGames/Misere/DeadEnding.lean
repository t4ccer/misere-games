import CombinatorialGames.GameForm
import CombinatorialGames.Misere.Outcome

namespace GameForm

def IsDeadEnd (g : GameForm) (p : Player) : Prop :=
  g.IsEnd p ∧ (∀ gp ∈ g.moves (-p), gp.IsDeadEnd p)
termination_by g
decreasing_by game_form_wf

def IsDeadEnd.IsEnd {g : GameForm} {p : Player} (h1 : g.IsDeadEnd p) : g.IsEnd p := by
  unfold IsDeadEnd at h1
  exact h1.left

def IsDeadEnd.moves {g : GameForm} {p : Player} (h1 : g.IsDeadEnd p) :
    ∀ gp ∈ g.moves (-p), gp.IsDeadEnd p := by
  unfold IsDeadEnd at h1
  exact h1.right

theorem IsDeadEnd.add {g h : GameForm} {p : Player} (h1 : g.IsDeadEnd p) (h2 : h.IsDeadEnd p) :
    (g + h).IsDeadEnd p := by
  unfold IsDeadEnd
  simp only [moves_add, Set.mem_union, Set.mem_image]
  apply And.intro (IsEnd.add_iff.mpr ⟨h1.IsEnd, h2.IsEnd⟩)
  intro gp h3
  apply Or.elim h3 <;> intro ⟨gpp, h3, h4⟩ <;> rw [<-h4]
  · exact IsDeadEnd.add (h1.moves gpp h3) h2
  · exact IsDeadEnd.add h1 (h2.moves gpp h3)
termination_by (g, h)
decreasing_by all_goals game_form_wf

private theorem lemma3.aux {g : GameForm} {p : Player} (h1 : g ≠ 0) (h2 : g.IsDeadEnd p) :
    MisereOutcome g = Outcome.ofPlayer p := by
  rw [MisereOutcome_eq_player_iff]
  apply And.intro (End_WinsGoingFirst h2.IsEnd)
  unfold WinsGoingFirst
  simp only [exists_prop, not_or, not_exists, not_and, not_not, neg_neg]
  apply And.intro (zero_not_both_end h1 h2.IsEnd)
  intro gr h4
  exact End_WinsGoingFirst (h2.moves gr h4).IsEnd

theorem lemma3_L (g : GameForm) (h1 : g ≠ 0) (h2 : g.IsDeadEnd .left) : MisereOutcome g = .L :=
  lemma3.aux h1 h2

theorem lemma3_R (g : GameForm) (h1 : g ≠ 0) (h2 : g.IsDeadEnd .right) : MisereOutcome g = .R :=
  lemma3.aux h1 h2

def IsDeadEnding (g : GameForm) : Prop :=
  (∀ p, g.IsEnd p → g.IsDeadEnd p) ∧ (∀ p, ∀gp ∈ g.moves p, gp.IsDeadEnding)
termination_by g
decreasing_by game_form_wf

@[simp]
theorem IsDeadEnding.IsDeadEnd {g : GameForm} {p : Player} (h1 : g.IsDeadEnding) (h2 : g.IsEnd p) :
    g.IsDeadEnd p := by
  unfold IsDeadEnding at h1
  exact h1.left p h2

@[simp]
theorem IsDeadEnding.moves {g h : GameForm} {p : Player} (h1 : g.IsDeadEnding) (h2 : h ∈ g.moves p) :
    h.IsDeadEnding := by
  unfold IsDeadEnding at h1
  exact h1.right p h h2

@[simp]
theorem IsDeadEnding.add {g h : GameForm} (h1 : g.IsDeadEnding) (h2 : h.IsDeadEnding) :
    (g + h).IsDeadEnding := by
  unfold IsDeadEnding
  simp only [moves_add, Set.mem_union, Set.mem_image]
  constructor <;> intro p
  · intro h3
    have ⟨h4, h5⟩ := IsEnd.add_iff.mp h3
    exact IsDeadEnd.add (h1.IsDeadEnd h4) (h2.IsDeadEnd h5)
  · intro gp h3
    apply Or.elim h3 <;> intro ⟨g', h3, h4⟩ <;> rw [<-h4]
    · exact IsDeadEnding.add (h1.moves h3) h2
    · exact IsDeadEnding.add h1 (h2.moves h3)
termination_by (g, h)
decreasing_by all_goals game_form_wf

end GameForm
