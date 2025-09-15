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

def IsDeadEnd.followers_IsDeadEnd {g : GameForm} {p : Player} (h1 : g.IsDeadEnd p) :
    ∀ gp ∈ g.moves (-p), gp.IsDeadEnd p := by
  unfold IsDeadEnd at h1
  exact h1.right

private theorem lemma3.aux {g : GameForm} {p : Player} (h1 : g ≠ 0) (h2 : g.IsDeadEnd p) :
    MisereOutcome g = Outcome.ofPlayer p := by
  rw [MisereOutcome_eq_player_iff]
  apply And.intro (End_WinsGoingFirst h2.IsEnd)
  unfold WinsGoingFirst
  simp only [exists_prop, not_or, not_exists, not_and, not_not, neg_neg]
  apply And.intro (zero_not_both_end h1 h2.IsEnd)
  intro gr h4
  exact End_WinsGoingFirst (h2.followers_IsDeadEnd gr h4).IsEnd

theorem lemma3_L (g : GameForm) (h1 : g ≠ 0) (h2 : g.IsDeadEnd .left) : MisereOutcome g = .L :=
  lemma3.aux h1 h2

theorem lemma3_R (g : GameForm) (h1 : g ≠ 0) (h2 : g.IsDeadEnd .right) : MisereOutcome g = .R :=
  lemma3.aux h1 h2

def IsDeadEnding (g : GameForm) : Prop :=
  (∀ p, g.IsEnd p → g.IsDeadEnd p) ∧ (∀ p, ∀gp ∈ g.moves p, gp.IsDeadEnding)
termination_by g
decreasing_by game_form_wf

-- theorem add_IsDeadEnd {g h : GameForm} {p : Player} (h1 : g.IsDeadEnd p)
end GameForm
