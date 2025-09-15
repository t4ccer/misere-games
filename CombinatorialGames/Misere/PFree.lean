import CombinatorialGames.GameForm
import CombinatorialGames.Misere.Outcome

namespace GameForm

def IsPFree (g : GameForm) : Prop :=
  (MisereOutcome g ≠ .P) ∧ (∀ p, ∀gp ∈ g.moves p, gp.IsPFree)
termination_by g
decreasing_by game_form_wf

def IsPFree.neg {g : GameForm} (h1 : g.IsPFree) : (-g).IsPFree := by
  unfold IsPFree at *
  obtain ⟨h1, h2⟩ := h1
  constructor
  · unfold MisereOutcome Outcome.ofPlayers
    simp only [outcome_eq_neg_player_conjugate, Player.neg_left, Player.neg_right, ne_eq]
    cases h3 : MiserePlayerOutcome g .left <;> cases h4 : MiserePlayerOutcome g .right
    <;> simp only [reduceCtorEq, not_false_eq_true, not_true_eq_false]
    refine h1 (wins_opposite_outcome_eq_P ?_)
    intro p
    cases p
    · exact h3
    · exact h4
  · intro p gp h3
    simp only [moves_neg, Set.involutiveNeg, Set.mem_neg] at h3
    have h4 := (h2 (-p) (-gp) h3).neg
    rw [neg_neg] at h4
    exact h4
termination_by g.birthday
decreasing_by
  rw [birthday_neg, <-birthday_neg g]
  exact birthday_lt_of_mem_moves h3

theorem IsPFree_moves {g h : GameForm} {p : Player} (h1 : g.IsPFree) (h2 : h ∈ g.moves p) :
    h.IsPFree := by
  unfold IsPFree at h1
  exact h1.right p h h2

theorem add_one_outcome_ne_P {g : GameForm} (h1 : g.IsPFree) : MisereOutcome (g + 1) ≠ .P := by
  sorry

theorem add_one_IsPFree {g : GameForm} (h1 : g.IsPFree) : (g + 1).IsPFree := by
  unfold IsPFree
  apply And.intro (add_one_outcome_ne_P h1)
  intro p
  simp only [moves_add, Set.mem_union, Set.mem_image]
  intro gp h2
  apply Or.elim h2 <;> intro h2
  · obtain ⟨k, h3, h4⟩ := h2
    rw [<-h4]
    have h5 : k.IsPFree := IsPFree_moves h1 h3
    exact add_one_IsPFree h5
  · cases p <;> simp only [Set.mem_empty_iff_false, Set.mem_singleton_iff, add_zero, exists_const,
                           exists_eq_left, false_and, leftMoves_one, rightMoves_one] at h2
    rw [<-h2]
    exact h1
termination_by g
decreasing_by game_form_wf

theorem add_int_IsPFree {g : GameForm} (h1 : g.IsPFree) (n : ℤ) : (g + n).IsPFree := by
  match n with
  | .ofNat m =>
    simp only [Int.ofNat_eq_coe, intCast_nat]
    induction m with
    | zero => simp only [Nat.cast_zero, add_zero, h1]
    | succ k ih => simp only [Nat.cast_add, Nat.cast_one, <-add_assoc, add_one_IsPFree ih]
  | .negSucc m =>
    have h2 : (-g + (m + 1)).IsPFree := by
      rw [<-add_assoc]
      exact add_one_IsPFree (add_int_IsPFree h1.neg m)
    have h3 := h2.neg
    simp only [neg_add_rev, neg_neg] at h3
    simp only [intCast_negSucc, neg_add_rev]
    rw [<-add_comm]
    exact h3
termination_by n.natAbs

end GameForm
