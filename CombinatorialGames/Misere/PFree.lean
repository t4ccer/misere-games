module

public import CombinatorialGames.AugmentedForm.Misere.Outcome
public import CombinatorialGames.GameForm.Misere.Outcome
public import CombinatorialGames.Form.Short

open Form
open Form.Misere.Outcome
open MisereForm

universe u

public section

class HasOne {G : Type (u + 1)} [Form G] (A : G → Prop) where
  has_one' : A 1

@[simp]
theorem has_one {G : Type (u + 1)} [Form G] {A : G → Prop} [HasOne A] : A 1 := HasOne.has_one'

@[expose] def IsPFree {G : Type (u + 1)} [Form G] [MisereForm G] (g : G) : Prop :=
  (MisereOutcome g ≠ .P) ∧ (∀ p, ∀gp ∈ moves p g, IsPFree gp)
termination_by g
decreasing_by form_wf

class OutcomeStable {G : Type (u + 1)} [Form G] [MisereForm G] (A : G → Prop) where
  outcome_LL_add (g h : G) (h1 : A g) (h2 : A h) (h3 : MisereOutcome g = .L) (h4 : MisereOutcome h = .L) :
    MisereOutcome (g + h) = .L
  outcome_RR_add (g h : G) (h1 : A g) (h2 : A h) (h3 : MisereOutcome g = .R) (h4 : MisereOutcome h = .R) :
    MisereOutcome (g + h) = .R
  player_outcome_LN_add (g h : G) (h1 : A g) (h2 : A h) (h3 : MisereOutcome g = .L) (h4 : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .left = .left
  player_outcome_RN_add (g h : G) (h1 : A g) (h2 : A h) (h3 : MisereOutcome g = .R) (h4 : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .right = .right

class PFree {G : Type (u + 1)} [Form G] [MisereForm G] (A : G → Prop)  where
  pfree {g : G} (h1 : A g) : IsPFree g

class HasNat {G : Type (u + 1)} [Form G] (A : G → Prop) extends HasOne A where
  has_nat (n : ℕ) : A (n : G)

class ClosedUnderAddNat {G : Type (u + 1)} [Form G] (A : G → Prop) where
  has_add {g : G} (h1 : A g) (n : ℕ) : A (g + n)

variable {G : Type (u + 1)} [Form G] [g_form : MisereForm G]

theorem IsPFree.MisereOutcome_ne_P {g : G} (h1 : IsPFree g) : MisereOutcome g ≠ .P := by
  unfold IsPFree at h1
  exact h1.left

private def IsPFree.neg {g : G} (h1 : IsPFree g) : IsPFree (-g) := by
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
decreasing_by gameform_birthday

@[simp]
theorem IsPFree.neg_iff {g : G} : IsPFree (-g) ↔ IsPFree g := by
  constructor <;> intro h1
  · rw [<-neg_neg g]
    exact h1.neg
  · exact h1.neg

theorem IsPFree_moves {g h : G} {p : Player} (h1 : IsPFree g) (h2 : h ∈ moves p g) :
    IsPFree h := by
  unfold IsPFree at h1
  exact h1.right p h h2

@[simp]
theorem IsPFree.IsOption {g g' : G} (h1 : IsPFree g) (h2 : Moves.IsOption g' g)
    : IsPFree g' := by
  rw [isOption_iff_mem_union, Set.mem_union] at h2
  apply Or.elim h2 <;> exact fun h2 => IsPFree_moves h1 h2

@[simp]
theorem IsPFree.zero : IsPFree (0 : GameForm) := by
  unfold IsPFree
  apply And.intro (by simp)
  simp only [moves_zero, Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]

@[simp]
theorem IsPFree.nat (n : ℕ) : IsPFree (n : GameForm) := by
  match n with
  | .zero => exact IsPFree.zero
  | .succ k =>
    unfold IsPFree
    have h2 : MisereOutcome ((k.succ : ℤ) : GameForm) ≠ Outcome.P := by simp
    exact And.intro h2 (GameForm.nat_forall_moves (IsPFree.nat k))

@[simp]
theorem IsPFree.int (k : ℤ) : IsPFree (k : GameForm) := by
  match k with
  | .ofNat n => simp only [Int.ofNat_eq_natCast, GameForm.intCast_nat, IsPFree.nat]
  | .negSucc n =>
    rw [Int.negSucc_eq, GameForm.intCast_neg, IsPFree.neg_iff]
    exact IsPFree.nat (n + 1)

@[simp]
theorem IsPFree.one : IsPFree (1 : GameForm) := by
  rw [<-GameForm.intCast_one]
  exact IsPFree.int 1

private def IsSpecial (g : G) : Prop :=
  ¬IsEnd Player.right g
  ∧ ∀ gr ∈ moves .right g,
      (MisereOutcome gr = Outcome.L) ∨ (∃ grl, ∃ (_ : grl ∈ moves .left gr), IsSpecial grl)
  termination_by g
  decreasing_by form_wf

private lemma special_implies_not_right_wins { g : GameForm } (h1: IsSpecial g) :
    ¬WinsGoingFirst .right g := by
  intro h2
  rw [GameForm.Misere.Outcome.WinsGoingFirst_iff] at h2
  cases h2 with
  | inl h_end =>
    unfold IsSpecial at h1
    exact h1.1 h_end
  | inr h_move =>
    obtain ⟨gr, hgr_mem, hgr_win⟩ := h_move
    unfold IsSpecial at h1
    cases h1.2 gr hgr_mem with
    | inl h_outcome_L =>
      rw [MisereOutcome_eq_L_iff] at h_outcome_L
      exact hgr_win h_outcome_L.left
    | inr h_left_special =>
      obtain ⟨grl, hgrl_mem, hgrl_special⟩ := h_left_special
      have h4 := special_implies_not_right_wins hgrl_special
      have h_left_wins_gr : WinsGoingFirst .left gr :=
        GameForm.Misere.Outcome.WinsGoingFirst_of_moves ⟨grl, hgrl_mem, h4⟩
      exact hgr_win h_left_wins_gr
      termination_by g
      decreasing_by form_wf

private lemma add_one_not_right_wins_implies_special {g : GameForm} (h1 : IsPFree g) (h2 :
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
      fun h_end => h2 (GameForm.Misere.Outcome.WinsGoingFirst_of_End h_end)

    -- If g were a Right end, then g+1 would also be a Right end (since 1 is a
    -- Right end)
    intro h_g_right_end
    apply h_g_plus_one_not_right_end
    rw [IsEnd_def] at h_g_right_end ⊢
    rw [moves_add, GameForm.rightMoves_one, Set.image_empty, Set.union_empty]
    simp only [Set.image_eq_empty]
    exact h_g_right_end
  · -- for each right move gr of g, show either gr has outcome L or ∃ special
    -- left move
    intro gr h_gr_mem
    -- 2. Let gr be an arbitrary Right move of g
    -- 3. Since gr is a Right move of g, we know that gr+1 is a Right move of
    -- g+1
    have h_gr_plus_one_mem : gr + 1 ∈ moves .right (g + 1) := by
      rw [moves_add]
      left
      use gr, h_gr_mem

    -- 4. Since Right does not win g+1 going first (by h2), we know that Left
    -- must win gr+1 going first
    have h_left_wins_gr_plus_one : WinsGoingFirst .left (gr + 1) := by
      by_contra h_left_not_wins
      apply h2
      apply GameForm.Misere.Outcome.WinsGoingFirst_of_moves
      use gr + 1, h_gr_plus_one_mem
      simp only [Player.neg_right]
      exact h_left_not_wins

    -- 5. Since 1 is not a Left end, gr+1 is not a Left end, so there must
    -- exist some winning move for Left from gr+1
    -- 6. This winning move is either to gr (by playing on 1), or to some
    -- grl+1, where grl is a Left move of gr
    rw [GameForm.Misere.Outcome.WinsGoingFirst_iff] at h_left_wins_gr_plus_one
    cases h_left_wins_gr_plus_one with
    | inl h_gr1_left_end =>
      have h_gr_is_left_move : gr ∈ moves .left (gr + 1) := by
        rw [moves_add, GameForm.leftMoves_one]
        right; simp
      simp only [IsEnd_def] at h_gr1_left_end
      rw [h_gr1_left_end] at h_gr_is_left_move
      exfalso
      exact h_gr_is_left_move
    | inr h_left_has_winning_move =>
      obtain ⟨winning_move, h_winning_mem, h_winning_wins⟩ := h_left_has_winning_move

      rw [moves_add] at h_winning_mem
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
  have h_g_is_left_move : g ∈ moves .left (g + 1) := by
    rw [moves_add, GameForm.leftMoves_one]
    right; simp

  -- 6. Since Right doesn't win g going first, Left wins g+1 going first
  have h_left_wins_g_plus_one : WinsGoingFirst .left (g + 1) := by
    apply GameForm.Misere.Outcome.WinsGoingFirst_of_moves
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
  simp only [moves_add, Set.mem_union, Set.mem_image]
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

@[aesop safe apply]
theorem add_nat_IsPFree {g : GameForm} (h1 : IsPFree g) (n : ℕ) : IsPFree (g + n) := by
  induction n with
  | zero => simp only [Nat.cast_zero, add_zero, h1]
  | succ k ih => simp only [Nat.cast_add, Nat.cast_one, <-add_assoc, add_one_IsPFree ih]

@[aesop safe apply]
theorem nat_add_IsPFree {g : GameForm} (h1 : IsPFree g) (n : ℕ) : IsPFree (n + g) := by
  rw [add_comm]
  exact add_nat_IsPFree h1 n

theorem add_int_IsPFree {g : GameForm} (h1 : IsPFree g) (n : ℤ) : IsPFree (g + n) := by
  match n with
  | .ofNat m => exact add_nat_IsPFree h1 m
  | .negSucc m =>
    rw [GameForm.intCast_negSucc, <-IsPFree.neg_iff, neg_add_rev, neg_neg, add_comm]
    exact add_nat_IsPFree h1.neg (m + 1)

theorem PFree.exists_move_WinsGoingFirst {g : GameForm} {p : Player}
    (h1 : ¬IsEnd p g) (h2 : IsPFree g) (h3 : WinsGoingFirst p g) :
    (∃gr ∈ moves p g, WinsGoingFirst p gr) := by
  rw [GameForm.Misere.Outcome.WinsGoingFirst_iff] at h3
  apply Or.elim h3 (fun h4 => False.elim (h1 h4))
  intro ⟨gr, h3, h4⟩
  use gr, h3
  by_cases h5 : WinsGoingFirst p gr
  · exact h5
  · have h6 : MisereOutcome gr = .P := MisereOutcome_eq_P_iff'.mpr ⟨h5, h4⟩
    have h7 : MisereOutcome gr ≠ .P := (IsPFree_moves h2 h3).MisereOutcome_ne_P
    exact False.elim (h7 h6)

mutual

theorem not_WinsGoingFirst_left_add_one {g : GameForm} (h0 : IsPFree g) (h1 : ¬WinsGoingFirst .left g) :
    ¬WinsGoingFirst .left (g + 1) := by
  intro h2
  rw [GameForm.Misere.Outcome.WinsGoingFirst_iff] at h2
  obtain h2 | ⟨gl, h2, h3⟩ := h2
  · have h3 := (IsEnd.add_iff.mp h2).right
    simp [IsEnd_def] at h3
  · rw [Player.neg_left] at h3
    simp at h2
    obtain h2 | ⟨gll, h2, h4⟩ := h2
    · rw [h2] at h3
      have h4 := MisereOutcome_eq_P_iff.mpr ⟨h3, h1⟩
      exact h0.MisereOutcome_ne_P h4
    · rw [<-h4] at h3
      have h5 : IsPFree gll := IsPFree_moves h0 h2
      have h6 := WinsGoingFirst_right_add_one h5 (by
        rw [GameForm.Misere.Outcome.WinsGoingFirst_iff] at h1
        simp at h1
        obtain ⟨h1, h6⟩ := h1
        exact h6 gll h2)
      exact h3 h6
termination_by g
decreasing_by form_wf

theorem WinsGoingFirst_right_add_one {g : GameForm} (h0 : IsPFree g) (h1 : WinsGoingFirst .right g) :
    WinsGoingFirst .right (g + 1) := by
  rw [GameForm.Misere.Outcome.WinsGoingFirst_iff] at h1
  obtain h1 | ⟨gr, h1, h2⟩ := h1
  · refine GameForm.Misere.Outcome.add_end_WinsGoingFirst h1 ?_
    simp [IsEnd_def]
  · refine GameForm.Misere.Outcome.WinsGoingFirst_of_moves ?_
    use (gr + 1)
    constructor
    · simp
      use gr
    · rw [Player.neg_right] at ⊢ h2
      exact not_WinsGoingFirst_left_add_one (IsPFree_moves h0 h1) h2
termination_by g
decreasing_by form_wf

end

@[aesop safe apply]
theorem MisereOutcome_add_one_R {g : GameForm} (h0 : IsPFree g) (h1 : MisereOutcome g = .R) :
    MisereOutcome (g + 1) = .R := by
  simp only [MisereOutcome_eq_R_iff]
  have ⟨h2, h3⟩ := MisereOutcome_eq_R_iff.mp h1
  constructor
  · exact WinsGoingFirst_right_add_one h0 h2
  · exact not_WinsGoingFirst_left_add_one h0 h3

@[aesop safe apply]
theorem MisereOutcome_add_nat_R {g : GameForm} (n : ℕ) (h0 : IsPFree g) (h1 : MisereOutcome g = .R) :
    MisereOutcome (g + n) = .R := by
  induction n with
  | zero => simp [h1]
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, <-add_assoc]
    exact MisereOutcome_add_one_R (add_nat_IsPFree h0 k) ih

mutual

theorem not_WinsGoingFirst_right_sub_one {g : GameForm} (h0 : IsPFree g) (h1 : ¬WinsGoingFirst .right g) :
    ¬WinsGoingFirst .right (g + (-1)) := by
  intro h2
  rw [GameForm.Misere.Outcome.WinsGoingFirst_iff] at h2
  obtain h2 | ⟨gl, h2, h3⟩ := h2
  · have h3 := (IsEnd.add_iff.mp h2).right
    simp [IsEnd_def] at h3
  · rw [Player.neg_right] at h3
    simp at h2
    obtain h2 | ⟨gll, h2, h4⟩ := h2
    · rw [h2] at h3
      have h4 := MisereOutcome_eq_P_iff.mpr ⟨h1, h3⟩
      exact h0.MisereOutcome_ne_P h4
    · rw [<-h4] at h3
      have h5 : IsPFree gll := IsPFree_moves h0 h2
      have h6 := WinsGoingFirst_left_sub_one h5 (by
        rw [GameForm.Misere.Outcome.WinsGoingFirst_iff] at h1
        simp at h1
        obtain ⟨h1, h6⟩ := h1
        exact h6 gll h2)
      exact h3 h6
termination_by g
decreasing_by form_wf

theorem WinsGoingFirst_left_sub_one {g : GameForm} (h0 : IsPFree g) (h1 : WinsGoingFirst .left g) :
    WinsGoingFirst .left (g + (-1)) := by
  rw [GameForm.Misere.Outcome.WinsGoingFirst_iff] at h1
  obtain h1 | ⟨gr, h1, h2⟩ := h1
  · refine GameForm.Misere.Outcome.add_end_WinsGoingFirst h1 ?_
    simp [IsEnd_def]
  · refine GameForm.Misere.Outcome.WinsGoingFirst_of_moves ?_
    use (gr + (-1))
    constructor
    · simp
      use gr
    · rw [Player.neg_left] at ⊢ h2
      exact not_WinsGoingFirst_right_sub_one (IsPFree_moves h0 h1) h2
termination_by g
decreasing_by form_wf

end

theorem MisereOutcome_sub_one_L {g : GameForm} (h0 : IsPFree g) (h1 : MisereOutcome g = .L) :
    MisereOutcome (g + (-1)) = .L := by
  simp only [MisereOutcome_eq_L_iff]
  have ⟨h2, h3⟩ := MisereOutcome_eq_L_iff.mp h1
  constructor
  · exact WinsGoingFirst_left_sub_one h0 h2
  · exact not_WinsGoingFirst_right_sub_one h0 h3

theorem MisereOutcome_sub_nat_L {g : GameForm} (n : ℕ) (h0 : IsPFree g) (h1 : MisereOutcome g = .L) :
    MisereOutcome (g + (-n)) = .L := by
  induction n with
  | zero => simp [h1]
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, neg_add_rev, add_comm (-1), <-add_assoc]
    refine MisereOutcome_sub_one_L ?_ ih
    rw [<-IsPFree.neg_iff, neg_add_rev, neg_neg, add_comm]
    exact add_nat_IsPFree (IsPFree.neg_iff.mpr h0) k

theorem OutcomeStable.outcome_LN_add {G : Type (u + 1)} [Form G] [MisereForm G] {A : G → Prop} [OutcomeStable A]
    (g h : G) (h1 : A g) (h2 : A h) (h3 : MisereOutcome g = .L) (h4 : MisereOutcome h = .N) :
    MisereOutcome (g + h) = .N ∨ MisereOutcome (g + h) = .L := by
  have h5 := player_outcome_LN_add g h h1 h2 h3 h4
  simp only [MisereOutcome, Outcome.ofPlayers, h5]
  cases MiserePlayerOutcome (g + h) Player.right
  <;> simp only [reduceCtorEq, or_true, or_false]

theorem OutcomeStable.outcome_RN_add {G : Type (u + 1)} [Form G] [MisereForm G] {A : G → Prop} [OutcomeStable A]
    {g h : G} (h1 : A g) (h2 : A h) (h3 : MisereOutcome g = .R) (h4 : MisereOutcome h = .N) :
    MisereOutcome (g + h) = .N ∨ MisereOutcome (g + h) = .R := by
  have h5 := player_outcome_RN_add g h h1 h2 h3 h4
  simp only [MisereOutcome, Outcome.ofPlayers, h5]
  cases MiserePlayerOutcome (g + h) Player.left
  <;> simp only [reduceCtorEq, or_true, or_false]

theorem PFree.IsPFree {G : Type (u + 1)} [Form G] [MisereForm G] {A : G → Prop} [PFree A] {g : G} (h1 : A g)
    : IsPFree g := PFree.pfree h1

@[simp]
theorem OutcomeStable.zero_ge_one {A : GameForm → Prop}
    [HasOne A] [OutcomeStable A] [PFree A] :
    0 ≥m A 1 := by
  rw [GameForm.Misere.Outcome.MisereGe]
  intro x h1
  rw [zero_add]
  cases h2 : MisereOutcome x
  · exact Outcome.L_ge (MisereOutcome (1 + x))
  · have h3 := OutcomeStable.outcome_RN_add has_one h1 GameForm.Misere.Outcome.one_MisereOutcome_R h2
    apply Or.elim h3 <;> intro h3 <;> simp only [h3, ge_iff_le, le_refl, Outcome.ge_R]
  · exact False.elim ((PFree.pfree h1).MisereOutcome_ne_P h2)
  · have h3 := OutcomeStable.outcome_RR_add
         (1 : GameForm) x
         has_one h1
         GameForm.Misere.Outcome.one_MisereOutcome_R h2
    rw [h3]

theorem ge_one_add_self {A : GameForm → Prop}
    [OutcomeStable A] [PFree A] [ClosedUnderAddNat A] [HasNat A]
    (n : ℕ) : n ≥m A (((1 : ℕ) + n) : ℕ) := by
  by_cases h1 : n > 0
  · rw [GameForm.Misere.Outcome.MisereGe]
    intro x h2
    simp only [Nat.cast_add, Nat.cast_one]
    rw [add_assoc _ _ x]
    nth_rw 2 [add_comm]
    cases h3 : MisereOutcome x
    · cases h4 : MisereOutcome (↑n + x)
      · simp only [ge_iff_le, Outcome.L_ge]
      · have h4' : A (n + x) := by
          have := (ClosedUnderAddNat.has_add h2 n)
          rwa [add_comm] at this
        have h5 := OutcomeStable.outcome_RN_add (A := A)
          has_one h4'
          GameForm.Misere.Outcome.one_MisereOutcome_R h4
        rw [add_comm]
        apply Or.elim h5 <;> intro h5 <;> simp only [ge_iff_le, Outcome.ge_R, le_refl, h5]
      · refine False.elim (IsPFree.MisereOutcome_ne_P ?_ h4)
        apply nat_add_IsPFree (PFree.IsPFree h2)
      · simp only [ge_iff_le, Outcome.le_R_iff]
        refine MisereOutcome_add_one_R ?_ h4
        apply nat_add_IsPFree (PFree.IsPFree h2)
    · have h4 := OutcomeStable.outcome_RN_add
        (HasNat.has_nat n) h2
        (GameForm.Misere.Outcome.pos_nat_MisereOutcome_R h1) h3
      apply Or.elim h4 <;> intro h4
      · have h4' : A (n + x) := by
          have := (ClosedUnderAddNat.has_add h2 n)
          rwa [add_comm] at this
        have h5 := OutcomeStable.outcome_RN_add
          has_one h4'
          (GameForm.Misere.Outcome.one_MisereOutcome_R) h4
        nth_rw 2 [add_comm]
        aesop
      · simp_all only [gt_iff_lt, reduceCtorEq, or_true, ge_iff_le, Outcome.le_R_iff]
        refine MisereOutcome_add_one_R ?_ h4
        apply nat_add_IsPFree (PFree.IsPFree h2)
    · refine False.elim (IsPFree.MisereOutcome_ne_P (PFree.pfree h2) h3)
    · have h4 := OutcomeStable.outcome_RR_add
         n x
         (HasNat.has_nat n) h2
         (GameForm.Misere.Outcome.pos_nat_MisereOutcome_R h1) h3
      simp only [ge_iff_le, Outcome.le_R_iff, h4]
      refine MisereOutcome_add_one_R ?_ h4
      apply nat_add_IsPFree (PFree.IsPFree h2)
  · simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h1
    simp only [h1, Nat.cast_zero, add_zero, Nat.cast_one, OutcomeStable.zero_ge_one]

theorem MisereGe_of_nat_le (A : GameForm → Prop)
    [OutcomeStable A] [PFree A] [ClosedUnderAddNat A] [HasNat A]
    (n m : ℕ) (h1 : n ≤ m) : n ≥m A m := by
  let k := m - n
  have h0 : m = n + k := by omega
  rw [h0]
  induction k with
  | zero => simp only [add_zero, GameForm.Misere.Outcome.MisereGe_refl]
  | succ k' ih =>
    apply GameForm.Misere.Outcome.MisereGe_trans ih
    rw [<-add_assoc, add_comm (n + k') 1]
    exact ge_one_add_self (n + k')

mutual

private theorem right_wins_of_birthday_le (g : GameForm) (b : ℕ) (h1 : birthday g ≤ b) :
    WinsGoingFirst .right (g + b) := by
  by_cases h2 : IsEnd .right g
  · exact GameForm.Misere.Outcome.add_end_WinsGoingFirst h2
      (GameForm.Misere.Outcome.nat_IsEnd_right b)
  · obtain ⟨gr, h3⟩ := Form.not_IsEnd_exists_move h2
    refine GameForm.Misere.Outcome.WinsGoingFirst_of_moves ?_
    refine ⟨gr + b, Form.add_right_mem_moves_add h3 b, ?_⟩
    exact not_left_wins_of_birthday_lt gr b ((Form.birthday_lt_of_mem_moves h3).trans_le h1)
termination_by g
decreasing_by form_wf

private theorem not_left_wins_of_birthday_lt (g : GameForm) (b : ℕ) (h1 : birthday g < b) :
    ¬WinsGoingFirst .left (g + b) := by
  have hbpos : 0 < b := by
    by_contra hb
    have : b = 0 := Nat.eq_zero_of_not_pos hb
    subst this
    simp at h1
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hbpos)
  rw [GameForm.Misere.Outcome.not_WinsGoingFirst]
  constructor
  · intro h2
    have h4 : ¬IsEnd .left ((k + 1 : ℕ) : GameForm) := by simp [IsEnd_def]
    exact h4 (by simpa [hk] using (IsEnd.add_iff.mp h2).right)
  · intro gl h2
    rw [moves_add] at h2
    rcases h2 with ⟨gl', h3, rfl⟩ | ⟨bl, h3, rfl⟩
    · exact right_wins_of_birthday_le gl' b (((Form.birthday_lt_of_mem_moves h3).trans h1).le)
    · have h6 : bl = (k : GameForm) := by
        simpa [hk, Nat.succ_eq_add_one] using h3
      rw [h6]
      have h7 : birthday g ≤ (k : ℕ) := by
        apply Order.lt_add_one_iff.mp
        simpa [hk, Nat.cast_add, Nat.cast_one] using h1
      by_cases h8 : IsEnd .right g
      · exact GameForm.Misere.Outcome.add_end_WinsGoingFirst h8
          (GameForm.Misere.Outcome.nat_IsEnd_right k)
      · obtain ⟨gr, h9⟩ := Form.not_IsEnd_exists_move h8
        refine GameForm.Misere.Outcome.WinsGoingFirst_of_moves ?_
        refine ⟨gr + k, Form.add_right_mem_moves_add h9 k, ?_⟩
        exact not_left_wins_of_birthday_lt gr k ((Form.birthday_lt_of_mem_moves h9).trans_le h7)
termination_by g
decreasing_by form_wf

end

private theorem add_gt_birthday_R (g : GameForm) (b : ℕ) (h1 : birthday g < b) :
    MisereOutcome (g + b) = .R := by
  exact MisereOutcome_eq_R_iff.mpr
    ⟨right_wins_of_birthday_le g b h1.le, not_left_wins_of_birthday_lt g b h1⟩

theorem add_birthday_plus_one_R (g : GameForm) (b : ℕ) (h1 : birthday g = b) :
    MisereOutcome (g + (b + (1 : ℕ))) = .R := by
  have h2 : (b : NatOrdinal) < (b + 1 : ℕ) := by
    simp
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using add_gt_birthday_R g (b + 1) (h1 ▸ h2)

theorem add_neg_birthday_plus_one_L (g : GameForm) (b : ℕ) (h1 : birthday g = b) :
    MisereOutcome (g + (-(b + (1 : ℕ)))) = .L := by
  simpa [outcome_conjugate_eq_outcome_neg, neg_add_rev, add_comm, add_left_comm, add_assoc] using
    congrArg Outcome.Conjugate
      (add_birthday_plus_one_R (-g) b (by simpa [Form.birthday_neg] using h1))

def RTippingPoint.aux (g : GameForm) [h1 : Short g] :
    ∃ (n : ℕ), MisereOutcome (g + n) = .R := by
  let ⟨b, h2⟩ := GameForm.short_iff_birthday_nat.mp h1
  use (b + 1)
  rw [Nat.cast_add]
  exact add_birthday_plus_one_R g b h2

def LTippingPoint.aux (g : GameForm) [h1 : Short g] :
    ∃ (n : ℕ), MisereOutcome (g + (-n)) = .L := by
  let ⟨b, h2⟩ := GameForm.short_iff_birthday_nat.mp h1
  use (b + 1)
  rw [Nat.cast_add]
  exact add_neg_birthday_plus_one_L g b h2

private theorem left_wins_second_implies_left_wins_first_add_one {g : GameForm}
    (h1 : ¬WinsGoingFirst .right g) : WinsGoingFirst .left (g + 1) := by
  refine GameForm.Misere.Outcome.WinsGoingFirst_of_moves ?_
  refine ⟨g, ?_, ?_⟩
  · rw [moves_add, GameForm.leftMoves_one]
    right
    refine ⟨0, by simp, by simp⟩
  · simpa [Player.neg_left] using h1

open scoped Classical in
private theorem exists_add_nat_N_of_not_R (g : GameForm) [Short g] (h1 : MisereOutcome g ≠ .R) :
    ∃ n : ℕ, MisereOutcome (g + n) = .N := by
  let hR : ∃ n : ℕ, MisereOutcome (g + n) = .R := RTippingPoint.aux g
  let r : ℕ := Nat.find hR
  have hrR : MisereOutcome (g + r) = .R := Nat.find_spec hR
  have hrpos : 0 < r := by
    by_contra h2
    have h3 : r = 0 := Nat.eq_zero_of_not_pos h2
    exact h1 (by simpa [r, h3, Nat.cast_zero, add_zero] using hrR)
  let n : ℕ := r - 1
  have hnsucc : n + 1 = r := by
    dsimp [n]
    omega
  have hnlt : n < r := by
    omega
  have hnotR_n : MisereOutcome (g + n) ≠ .R := by
    exact Nat.find_min hR (by simpa [r] using hnlt)
  have hnotLeft_r : ¬WinsGoingFirst .left (g + r) := (MisereOutcome_eq_R_iff.mp hrR).2
  have hright_n : WinsGoingFirst .right (g + n) := by
    by_contra h2
    have h3 : WinsGoingFirst .left ((g + n) + 1) :=
      left_wins_second_implies_left_wins_first_add_one h2
    have h4 : WinsGoingFirst .left (g + (n + 1 : ℕ)) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using h3
    exact hnotLeft_r (by simpa [hnsucc] using h4)
  refine ⟨n, ?_⟩
  cases hn : MisereOutcome (g + n)
  · exact False.elim ((MisereOutcome_eq_L_iff.mp hn).right hright_n)
  · simp
  · exact False.elim ((MisereOutcome_eq_P_iff.mp hn).left hright_n)
  · exact False.elim (hnotR_n hn)

def NTippingPoint.aux (g : GameForm) [h1 : Short g] :
    ∃ (n : ℕ), MisereOutcome (g + n) = .N ∨ MisereOutcome (g + (-n)) = .N := by
  by_cases h2 : MisereOutcome g = .R
  · have h3 : MisereOutcome (-g) = .L := by simp [h2]
    obtain ⟨n, hn⟩ := exists_add_nat_N_of_not_R (-g) (by simp [h3])
    refine ⟨n, Or.inr ?_⟩
    have h4 : (MisereOutcome (-g + n)).Conjugate = .N := by
      rw [hn]
      rfl
    simpa [outcome_conjugate_eq_outcome_neg, neg_add_rev, add_comm, add_left_comm, add_assoc] using h4
  · obtain ⟨n, hn⟩ := exists_add_nat_N_of_not_R g h2
    exact ⟨n, Or.inl hn⟩

open scoped Classical in
noncomputable def NTippingPoint (g : GameForm) [Short g] : ℕ :=
  Nat.find (NTippingPoint.aux g)

theorem NTippingPoint.neg (g : GameForm) [Short g] : NTippingPoint g = NTippingPoint (-g) := by
  classical
  unfold NTippingPoint
  apply Nat.find_congr'
  intro n
  have hconjN : ∀ x : GameForm, MisereOutcome x = .N ↔ MisereOutcome (-x) = .N := by
    intro x
    constructor <;> intro hx
    · have : (MisereOutcome x).Conjugate = .N := by rw [hx]; rfl
      simpa [outcome_conjugate_eq_outcome_neg] using this
    · have : (MisereOutcome (-x)).Conjugate = .N := by rw [hx]; rfl
      simpa [outcome_conjugate_eq_outcome_neg] using this
  have h1 : MisereOutcome (g + n) = .N ↔ MisereOutcome (-g + (-n)) = .N := by
    simpa [neg_add_rev, add_comm, add_left_comm, add_assoc] using hconjN (g + n)
  have h2 : MisereOutcome (g + (-n)) = .N ↔ MisereOutcome (-g + n) = .N := by
    simpa [neg_add_rev, add_comm, add_left_comm, add_assoc] using hconjN (g + (-n))
  constructor <;> intro h
  · simpa [or_comm] using Or.imp h1.mp h2.mp h
  · simpa [or_comm] using Or.imp h2.mpr h1.mpr h

open scoped Classical in
noncomputable def RTippingPoint (g : GameForm) [Short g] : ℕ :=
  Nat.find (RTippingPoint.aux g)

open scoped Classical in
theorem RTippingPoint_iff (g : GameForm) [Short g] (n : ℕ) :
    (RTippingPoint g = n)
     ↔ ((MisereOutcome (g + n) = .R) ∧ ∀ (x : ℕ), MisereOutcome (g + x) = .R → n ≤ x) := by
  unfold RTippingPoint
  rw [Nat.find_eq_iff]
  constructor <;> intro ⟨h2, h3⟩ <;> apply And.intro h2 <;> intro x h4
  · exact Nat.le_of_not_lt fun h5 ↦ h3 x h5 h4
  · intro h5
    have h6 := h3 x h5
    omega

open scoped Classical in
noncomputable def LTippingPoint (g : GameForm) [Short g] : ℕ :=
  Nat.find (LTippingPoint.aux g)

open scoped Classical in
theorem LTippingPoint_iff (g : GameForm) [Short g] (n : ℕ) :
    (LTippingPoint g = n)
     ↔ ((MisereOutcome (g + (-n)) = .L) ∧ ∀ (x : ℕ), MisereOutcome (g + (-x)) = .L → n ≤ x) := by
  unfold LTippingPoint
  rw [Nat.find_eq_iff]
  constructor <;> intro ⟨h2, h3⟩ <;> apply And.intro h2 <;> intro x h4
  · exact Nat.le_of_not_lt fun h5 ↦ h3 x h5 h4
  · intro h5
    have h6 := h3 x h5
    omega

-- augmented form versions

private def IsSpecial_aug (g : AugmentedForm) : Prop :=
  ¬AugmentedForm.EndLike Player.right g
  ∧ ∀ gr ∈ moves .right g,
      (MisereOutcome gr = Outcome.L) ∨ (∃ grl, ∃ (_ : grl ∈ moves .left gr), IsSpecial_aug grl)
  termination_by g
  decreasing_by form_wf

private lemma special_implies_not_right_wins_aug { g : AugmentedForm } (h1: IsSpecial_aug g) :
    ¬WinsGoingFirst .right g := by
  unfold IsSpecial_aug at h1
  obtain ⟨h_not_right_EndLike, h2⟩ := h1
  -- 0. g is not Right end-like, so Right does not win immediately going first
  rw [AugmentedForm.not_WinsGoingFirst]
  apply And.intro h_not_right_EndLike
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
    apply AugmentedForm.WinsGoingFirst_of_moves
    use grl, h_grl_mem_left, h_not_right_grl
termination_by g
decreasing_by form_wf

private lemma add_one_not_right_wins_implies_special_aug {g : AugmentedForm} (h1 : IsPFree g) (h2 :
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
