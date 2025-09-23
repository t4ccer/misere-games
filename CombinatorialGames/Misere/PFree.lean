import CombinatorialGames.AugmentedForm.Misere.Outcome
import CombinatorialGames.GameForm.Misere.Outcome

open Form
open Form.Misere.Outcome
open MisereForm

universe u
variable {G : Type (u + 1)} [g_form : MisereForm G]

def IsPFree (g : G) : Prop :=
  (MisereOutcome g ≠ .P) ∧ (∀ p, ∀gp ∈ moves p g, IsPFree gp)
termination_by g
decreasing_by form_wf

def IsPFree.neg {g : G} (h1 : IsPFree g) : IsPFree (-g) := by
  unfold IsPFree at *
  obtain ⟨h1, h2⟩ := h1
  constructor
  · unfold MisereOutcome Outcome.ofPlayers
    simp only [outcome_eq_neg_player_conjugate,
               Player.neg_left, Player.neg_right, ne_eq]
    cases h3 : MiserePlayerOutcome g .left <;> cases h4 : MiserePlayerOutcome g .right
    <;> simp only [reduceCtorEq, not_false_eq_true, not_true_eq_false]
    refine h1 (wins_opposite_outcome_eq_P ?_)
    intro p
    cases p
    · exact h3
    · exact h4
  · intro p gp h3
    simp only [moves_neg, Set.mem_neg] at h3
    have h4 := (h2 (-p) (-gp) h3).neg
    rw [neg_neg] at h4
    exact h4
termination_by birthday g
decreasing_by
  rw [Form.birthday_neg, <-Form.birthday_neg g]
  exact Form.birthday_lt_of_mem_moves h3

theorem IsPFree_moves {g h : G} {p : Player} (h1 : IsPFree g) (h2 : h ∈ moves p g) :
    IsPFree h := by
  unfold IsPFree at h1
  exact h1.right p h h2

private def IsSpecial (g : G) : Prop :=
  ¬IsEnd Player.right g
  ∧ ∀ gr ∈ moves .right g,
      (MisereOutcome gr = Outcome.L) ∨ (∃ grl, ∃ (_ : grl ∈ moves .left gr), IsSpecial grl)
  termination_by g
  decreasing_by form_wf

private lemma special_implies_not_right_wins { g : GameForm } (h1: IsSpecial g) :
    ¬WinsGoingFirst .right g := by
  intro h2
  rw [GameForm.Misere.Outcome.WinsGoingFirst_def] at h2
  cases h2 with
  | inl h_end =>
    unfold IsSpecial at h1
    exact h1.1 h_end
  | inr h_move =>
    obtain ⟨gr, hgr_mem, hgr_win⟩ := h_move
    unfold IsSpecial at h1
    cases h1.2 gr hgr_mem with
    | inl h_outcome_L => aesop
    | inr h_left_special =>
      obtain ⟨grl, hgrl_mem, hgrl_special⟩ := h_left_special
      have h4 := special_implies_not_right_wins hgrl_special
      have h_left_wins_gr : WinsGoingFirst .left gr := by
        rw [GameForm.Misere.Outcome.WinsGoingFirst_def]
        right
        exact ⟨grl, hgrl_mem, h4⟩
      exact hgr_win h_left_wins_gr
      termination_by g
      decreasing_by form_wf

lemma add_one_not_right_wins_implies_special {g : GameForm} (h1 : IsPFree g) (h2 :
    ¬WinsGoingFirst .right (g + 1)) : IsSpecial g := by
      /- proof strategy:
        0. Right does not win going first on g+1 (by h2), which means g+1
        cannot be a Right end.
        1. Since g+1 is not a Right end, g cannot be a Right end.
        2. Let gr be an arbitrary Right move of g.
        3. Since gr is a Right move of g, we know that gr+1 is a Right move of
        g+1.
        4. Since Right does not win g+1 going first (by h2), we know that Left
        must win gr+1 going first.
        5. Since 1 is not a Left end, gr+1 is not a Left end, so there must
        exist some winning move for Left from gr+1.
        6. This winning move is either to gr (by playing on 1), or to some
        grl+1, where grl is a Left move of gr.
        7. Assume first that the winning move is to gr (by playing on 1):
          8. Since this is a winning move for Left (from gr+1), it follows that
          gr must have outcome L or P.
          9. Since g is p-free (h1), we know that gr is p-free.
          10. So, gr must have outcome L.
        11. Assume instead now that the winning move is to some grl+1:
          12. Since this move is winning for Left (from gr+1), we know that
          Right does not win going first on grl+1.
          13. Since grl is p-free (h1), we know that grl is p-free.
          14. By induction, we must have grl.IsSpecial.
      -/
  unfold IsSpecial
  constructor
    -- 0: Right does not win going first on g+1 (by h2), which means g+1
    -- cannot be a Right end
  · -- 1. Since g+1 is not a Right end, g cannot be a Right end
    have h_g_plus_one_not_right_end : ¬IsEnd Player.right (g + 1) :=
      fun h_end => h2 (GameForm.Misere.Outcome.End_WinsGoingFirst h_end)

    -- If g were a Right end, then g+1 would also be a Right end (since 1 is a
    -- Right end)
    intro h_g_right_end
    apply h_g_plus_one_not_right_end
    unfold IsEnd at h_g_right_end ⊢
    simp only [Form.moves]
    rw [GameForm.moves_add, GameForm.rightMoves_one, Set.image_empty, Set.union_empty]
    simp only [Set.image_eq_empty]
    simp only [Form.moves] at h_g_right_end
    rw [h_g_right_end]

  · -- for each right move gr of g, show either gr has outcome L or ∃ special
    -- left move
    intro gr h_gr_mem
    -- 2. Let gr be an arbitrary Right move of g
    -- 3. Since gr is a Right move of g, we know that gr+1 is a Right move of
    -- g+1
    have h_gr_plus_one_mem : gr + 1 ∈ (g + 1).moves Player.right := by
      rw [GameForm.moves_add]
      left
      use gr, h_gr_mem

    -- 4. Since Right does not win g+1 going first (by h2), we know that Left
    -- must win gr+1 going first
    have h_left_wins_gr_plus_one : WinsGoingFirst .left (gr + 1) := by
      by_contra h_left_not_wins
      apply h2
      rw [GameForm.Misere.Outcome.WinsGoingFirst_def]
      right
      use gr + 1, h_gr_plus_one_mem
      simp only [Player.neg_right]
      exact h_left_not_wins

    -- 5. Since 1 is not a Left end, gr+1 is not a Left end, so there must
    -- exist some winning move for Left from gr+1
    -- 6. This winning move is either to gr (by playing on 1), or to some
    -- grl+1, where grl is a Left move of gr
    rw [GameForm.Misere.Outcome.WinsGoingFirst_def] at h_left_wins_gr_plus_one
    cases h_left_wins_gr_plus_one with
    | inl h_gr1_left_end =>
      have h_gr_is_left_move : gr ∈ (gr + 1).moves Player.left := by
        rw [GameForm.moves_add, GameForm.leftMoves_one, GameForm.moves]
        right; simp
      simp only [moves, IsEnd] at h_gr1_left_end
      rw [h_gr1_left_end] at h_gr_is_left_move
      exfalso
      exact h_gr_is_left_move
    | inr h_left_has_winning_move =>
      obtain ⟨winning_move, h_winning_mem, h_winning_wins⟩ := h_left_has_winning_move

      rw [moves_add] at h_winning_mem
      simp only [moves] at h_winning_mem
      rw [GameForm.leftMoves_one] at h_winning_mem
      simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at h_winning_mem

      cases h_winning_mem with
      | inl h_winning_from_gr =>
        obtain ⟨grl, h_grl_mem, h_winning_eq⟩ := h_winning_from_gr
        -- 11. Assume the winning move is to some grl+1
        -- 12. Since this move is winning for Left (from gr+1), Right does not
        -- win going first on grl+1
        rw [← h_winning_eq] at h_winning_wins
        simp only [Player.neg_left] at h_winning_wins
        have h_right_not_wins_grl_plus_one : ¬WinsGoingFirst .right (grl + 1) := h_winning_wins

        -- 13. Since grl is p-free (h1), we know that grl is p-free
        have h_grl_pfree : IsPFree grl := by
          have h_gr_pfree : IsPFree gr := IsPFree_moves h1 h_gr_mem
          exact IsPFree_moves h_gr_pfree h_grl_mem

        -- 14. By induction, we must have grl.IsSpecial
        right
        use grl, h_grl_mem
        exact add_one_not_right_wins_implies_special h_grl_pfree h_right_not_wins_grl_plus_one

      | inr h_winning_is_gr =>
        -- 7. Assume the winning move is to gr (by playing on 1)
        simp at h_winning_is_gr
        rw [← h_winning_is_gr] at h_winning_wins
        simp only [Player.neg_left] at h_winning_wins
        have h_right_not_wins_gr : ¬WinsGoingFirst .right gr := h_winning_wins

        -- 8. Since this is a winning move for Left (from gr+1), gr must have
        -- outcome L or P
        -- 9. Since g is p-free (h1), we know that gr is p-free
        have h_gr_pfree : IsPFree gr := IsPFree_moves h1 h_gr_mem

        -- 10. So, gr must have outcome L
        left
        unfold IsPFree at h_gr_pfree
        obtain ⟨h_gr_ne_P, _⟩ := h_gr_pfree

        have h_gr_cases : MisereOutcome gr = .L ∨ MisereOutcome gr = .R ∨ MisereOutcome gr = .N := by
          cases h : MisereOutcome gr <;> tauto

        cases h_gr_cases with
        | inl h_L => exact h_L
        | inr h_rest =>
          cases h_rest with
          | inl h_R =>
            exfalso
            rw [MisereOutcome_eq_R_iff] at h_R
            obtain ⟨h_right_wins_gr, _⟩ := h_R
            exact h_right_not_wins_gr h_right_wins_gr
          | inr h_N =>
            exfalso
            have h_right_wins_gr : WinsGoingFirst .right gr := by
              unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h_N
              by_cases h_right : WinsGoingFirst .right gr
              · exact h_right
              · by_cases h_left : WinsGoingFirst .left gr
                <;> simp only [h_left, h_right, reduceIte, reduceCtorEq] at h_N
            exact h_right_not_wins_gr h_right_wins_gr
            termination_by g
            decreasing_by form_wf

theorem add_one_outcome_ne_P {g : GameForm} (h1 : IsPFree g) : MisereOutcome (g + 1) ≠ .P := by
  /- proof strategy:
      0. Assume for a contradiction that g+1 has outcome P.
      1. This means that Right does not win g+1 going first.
      2. By add_one_P_gives_special, we know that g.IsSpecial.
      3. By SpecialImpliesWin, we know that Right does not win g going first.
      4. We will now show that Left wins g+1 going first.
      5. Left can play on g+1 to g (by playing on 1).
      6. We know that Right does not win g going first, and so Left wins g+1
      going first (by playing on 1 to leave g).
      7. But we assumed that g+1 had outcome P, which means Left does not win
      g+1 going first: this is a contradiction.
  -/
  intro h_outcome_P
  -- 0. Assume for contradiction that g+1 has outcome P
  -- 1. This means Right does not win g+1 going first
  have h_right_not_wins_g1 : ¬WinsGoingFirst .right (g + 1) :=
    outcome_eq_P_not_WinsGoingFirst h_outcome_P

  -- 2. By add_one_P_gives_special, g is special
  have h_g_special : IsSpecial g := add_one_not_right_wins_implies_special h1 h_right_not_wins_g1

  -- 3. By SpecialImpliesWin, Right does not win g going first
  have h_right_not_wins_g : ¬WinsGoingFirst .right g := special_implies_not_right_wins h_g_special

  -- 4. We will now show that Left wins g+1 going first.
  -- 5. Left can play on g+1 to g (by playing on 1)
  have h_g_is_left_move : g ∈ (g + 1).moves Player.left := by
    rw [GameForm.moves_add, GameForm.leftMoves_one]
    right; simp

  -- 6. Since Right doesn't win g going first, Left wins g+1 going first
  have h_left_wins_g_plus_one : WinsGoingFirst .left (g + 1) := by
    rw [GameForm.Misere.Outcome.WinsGoingFirst_def]
    right
    use g, h_g_is_left_move, h_right_not_wins_g

  -- 7. But we assumed that g+1 had outcome P, which means Left does not win
  -- g+1 going first: this is a contradiction.
  have h_left_not_wins_g_plus_one : ¬WinsGoingFirst .left (g + 1) :=
    outcome_eq_P_not_WinsGoingFirst h_outcome_P

  exact h_left_not_wins_g_plus_one h_left_wins_g_plus_one

theorem add_one_IsPFree {g : GameForm} (h1 : IsPFree g) : IsPFree (g + 1) := by
  unfold IsPFree
  apply And.intro (add_one_outcome_ne_P h1)
  intro p
  simp only [GameForm.moves_add, Set.mem_union, Set.mem_image, moves]
  intro gp h2
  apply Or.elim h2 <;> intro h2
  · obtain ⟨k, h3, h4⟩ := h2
    rw [<-h4]
    have h5 : IsPFree k := IsPFree_moves h1 h3
    exact add_one_IsPFree h5
  · cases p <;> simp only [Set.mem_empty_iff_false, Set.mem_singleton_iff, add_zero, exists_const,
                           exists_eq_left, false_and,
                           GameForm.leftMoves_one, GameForm.rightMoves_one] at h2
    rw [<-h2]
    exact h1
termination_by g
decreasing_by form_wf

theorem add_int_IsPFree {g : GameForm} (h1 : IsPFree g) (n : ℤ) : IsPFree (g + n) := by
  match n with
  | .ofNat m =>
    simp only [Int.ofNat_eq_coe, GameForm.intCast_nat]
    induction m with
    | zero => simp only [Nat.cast_zero, add_zero, h1]
    | succ k ih => simp only [Nat.cast_add, Nat.cast_one, <-add_assoc, add_one_IsPFree ih]
  | .negSucc m =>
    have h2 : IsPFree (-g + (m + 1)) := by
      rw [<-add_assoc]
      exact add_one_IsPFree (add_int_IsPFree h1.neg m)
    have h3 := h2.neg
    simp only [neg_add_rev, neg_neg] at h3
    simp only [GameForm.intCast_negSucc, neg_add_rev]
    rw [<-add_comm]
    exact h3
termination_by n.natAbs

-- augmented form versions

private def IsSpecial_aug (g : AugmentedForm) : Prop :=
  ¬AugmentedForm.EndLike g Player.right
  ∧ ∀ gr ∈ moves .right g,
      (MisereOutcome gr = Outcome.L) ∨ (∃ grl, ∃ (_ : grl ∈ moves .left gr), IsSpecial_aug grl)
  termination_by g
  decreasing_by form_wf

private lemma special_implies_not_right_wins_aug { g : AugmentedForm } (h1: IsSpecial_aug g) :
    ¬WinsGoingFirst .right g := by
  unfold IsSpecial_aug at h1
  obtain ⟨h1, h2⟩ := h1
  simp only [WinsGoingFirst]
  unfold AugmentedForm.WinsGoingFirst'
  simp only [Player.neg_right, exists_prop, not_or, not_exists, not_and, not_not]
  -- 0. g is not Right end-like, so Right does not win immediately going first
  apply And.intro h1
  -- 1. consider any right move gr of g
  intro gr h_gr_mem_right
  -- 2. since g is special, we have two cases:
  obtain h_outcome_eq_L | h4 := h2 gr h_gr_mem_right
  · -- 3. gr has outcome L
    -- 4. then Left wins
    exact (MisereOutcome_eq_L_iff.mp h_outcome_eq_L).left
  · -- 5. there exists a left move grl of gr that is special
    obtain ⟨grl, h_grl_mem_left, h_grl_special⟩ := h4
    -- 6. by induction, right does not win going first on grl, so Left wins
    have h_not_right_grl : ¬WinsGoingFirst .right grl :=
      special_implies_not_right_wins_aug h_grl_special
    unfold AugmentedForm.WinsGoingFirst'
    exact Or.inr (BEx.intro grl h_grl_mem_left h_not_right_grl)
termination_by g
decreasing_by form_wf

lemma add_one_not_right_wins_implies_special_aug {g : AugmentedForm} (h1 : IsPFree g) (h2 :
    ¬WinsGoingFirst .right (g + (1 : GameForm))) : IsSpecial_aug g := by
      /- proof strategy:
        0. Right does not win going first on g+1 (by h2), which means g+1
        cannot be Right end-like.
        1. Since g+1 is not Right end-like, g cannot be Right end-like
        (EndLike_add_iff).
        2. Let gr be an arbitrary Right move of g.
        3. Since gr is a Right move of g, we know that gr+1 is a Right move of
        g+1.
        4. Since Right does not win g+1 going first (by h2), we know that Left
        must win gr+1 going first.
        5. Since 1 is not Left end-like, gr+1 is not Left end-like
        (EndLike_add_iff), so there must exist some winning move for Left from
        gr+1.
        6. This winning move is either to gr (by playing on 1), or to some
        grl+1, where grl is a Left move of gr.
        7. Assume first that the winning move is to gr (by playing on 1):
          8. Since this is a winning move for Left (from gr+1), it follows that
          gr must have outcome L or P.
          9. Since g is p-free (h1), we know that gr is p-free.
          10. So, gr must have outcome L.
        11. Assume instead now that the winning move is to some grl+1:
          12. Since this move is winning for Left (from gr+1), we know that
          Right does not win going first on grl+1.
          13. Since grl is p-free (h1), we know that grl is p-free.
          14. By induction, we must have grl.IsSpecial.
      -/
  sorry

theorem add_one_outcome_ne_P_aug {g : AugmentedForm} (h1 : IsPFree g) : MisereOutcome (g + (1 : GameForm)) ≠ .P := by
  /- proof strategy:
      (same as for GameForm from before)
      0. Assume for a contradiction that g+1 has outcome P.
      1. This means that Right does not win g+1 going first.
      2. By add_one_P_gives_special, we know that g.IsSpecial.
      3. By SpecialImpliesWin, we know that Right does not win g going first.
      4. We will now show that Left wins g+1 going first.
      5. Left can play on g+1 to g (by playing on 1).
      6. We know that Right does not win g going first, and so Left wins g+1
      going first (by playing on 1 to leave g).
      7. But we assumed that g+1 had outcome P, which means Left does not win
      g+1 going first: this is a contradiction.
  -/
  sorry
