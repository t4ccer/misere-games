import CombinatorialGames.Misere.Outcome
import CombinatorialGames.Misere.DeadEnding

namespace GameForm

def IsBlockedEnd (g : GameForm) (p : Player) : Prop :=
  (g.IsEnd p)
    ∧ (∀ gr ∈ g.moves (-p),
         (gr.IsBlockedEnd p
         ∨ (∃ grl,∃ (_ : grl ∈ gr.moves p), grl.IsBlockedEnd p)))
termination_by g
decreasing_by all_goals game_form_wf

def IsBlocking (g : GameForm) : Prop :=
  (∀ p, g.IsEnd p → g.IsBlockedEnd p) ∧ (∀ p, ∀gp ∈ g.moves p, gp.IsBlocking)
termination_by g
decreasing_by game_form_wf

class ClosedUnderSum (A : GameForm → Prop) where
  closed_sum (g h : GameForm) (h1 : A g) (h2 : A h) : A (g + h)

class ClosedUnderFollower (A : GameForm → Prop) where
  closed_follower (g : GameForm) (h1 : A g) : ∀g', g'.IsOption g → A g'

class NoP (A : GameForm → Prop) where
  no_P (g : GameForm) (h1 : A g) : MisereOutcome g ≠ .P

class DeadEnding (A : GameForm → Prop) where
  dead_ending (g : GameForm) : g.IsDeadEnding

theorem theorem4 {A : GameForm → Prop} [ClosedUnderNeg A] [ClosedUnderSum A]
    [ClosedUnderFollower A] [DeadEnding A] [NoP A] (g : GameForm) (h1 : A g) :
    g + (-g) =m A 0 := by
  sorry

end GameForm
