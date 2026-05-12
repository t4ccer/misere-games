module

public import CombinatorialGames.Form.Misere.Outcome
public import CombinatorialGames.GameForm

open Form
open Form.Misere.Outcome
open GameForm

universe u

public section

@[expose] def IsPFree {G : Type (u + 1)} [Form G] (g : G) : Prop :=
  (MisereOutcome g ≠ .P) ∧ (∀ p, ∀gp ∈ moves p g, IsPFree gp)
termination_by g
decreasing_by form_wf

class PFree {G : Type (u + 1)} [Form G] (A : G → Prop)  where
  pfree {g : G} (h1 : A g) : IsPFree g

instance {G : Type (u + 1)} [Form G] : PFree (G := G) IsPFree where
  pfree := id

class HasNat {G : Type (u + 1)} [Form G] (A : G → Prop) where
  has_nat (n : ℕ) : A (n : G)

class HasInt (A : GameForm → Prop) extends HasNat A where
  has_int (n : ℤ) : A (n : GameForm)

@[simp]
theorem has_one {A : GameForm → Prop} [HasNat A] : A 1 := by
  rw [<-Form.natCast_one]
  exact HasNat.has_nat 1

class ClosedUnderAddNat {G : Type (u + 1)} [Form G] (A : G → Prop) where
  has_add {g : G} (h1 : A g) (n : ℕ) : A (g + n)

variable {G : Type (u + 1)} [Form G]

private def IsPFree.neg {g : G} (h1 : IsPFree g) : IsPFree (-g) := by
  unfold IsPFree at *
  obtain ⟨h1, h2⟩ := h1
  constructor
  · unfold MisereOutcome Outcome.ofPlayers
    simp only [miserePlayerOutcome_neg_player_neg,
               Player.neg_left, Player.neg_right, ne_eq]
    cases h3 : MiserePlayerOutcome g .left <;> cases h4 : MiserePlayerOutcome g .right
    <;> simp only [reduceCtorEq, not_false_eq_true, not_true_eq_false]
    refine h1 (misereOutcome_P_of_miserePlayerOutcome_neg ?_)
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

instance : ClosedUnderNeg (IsPFree (G := G)) where
  neg_of := IsPFree.neg

theorem isPFree_of_mem_moves {g h : G} {p : Player} (h1 : IsPFree g) (h2 : h ∈ moves p g) :
    IsPFree h := by
  unfold IsPFree at h1
  exact h1.right p h h2

theorem isPFree_of_isOption {g g' : G} (h1 : IsPFree g) (h2 : Moves.IsOption g' g)
    : IsPFree g' := by
  rw [isOption_iff_mem_union, Set.mem_union] at h2
  apply Or.elim h2 <;> exact fun h2 => isPFree_of_mem_moves h1 h2

@[simp]
theorem isPFree_zero : IsPFree (0 : GameForm) := by
  unfold IsPFree
  apply And.intro (by simp)
  simp only [moves_zero (G := GameForm), Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]

@[simp]
theorem isPFree_natCast (n : ℕ) : IsPFree (n : GameForm) := by
  match n with
  | .zero => exact isPFree_zero
  | .succ k =>
    unfold IsPFree
    have h2 : MisereOutcome ((k.succ : ℤ) : GameForm) ≠ Outcome.P := by simp
    exact And.intro h2 (nat_forall_moves (isPFree_natCast k))

@[simp]
theorem isPFree_intCast (k : ℤ) : IsPFree (k : GameForm) := by
  match k with
  | .ofNat n => simp only [Int.ofNat_eq_natCast, Form.intCast_nat, isPFree_natCast]
  | .negSucc n =>
    rw [Int.negSucc_eq, Form.intCast_neg, ClosedUnderNeg.neg_iff (A := IsPFree)]
    exact isPFree_natCast (n + 1)

@[simp]
theorem isPFree_one : IsPFree (1 : GameForm) := by
  rw [<-Form.intCast_one]
  exact isPFree_intCast 1

private def IsSpecial (g : G) : Prop :=
  ¬IsEnd Player.right g
  ∧ ∀ gr ∈ moves .right g,
      (MisereOutcome gr = Outcome.L) ∨ (∃ grl, ∃ (_ : grl ∈ moves .left gr), IsSpecial grl)
  termination_by g
  decreasing_by form_wf

private lemma not_winsGoingFirst_right_of_isSpecial {g : GameForm} (h1: IsSpecial g)
    : ¬WinsGoingFirst .right g := by
  intro h2
  rw [winsGoingFirst_iff] at h2
  cases h2 with
  | inl h_end =>
    unfold IsSpecial at h1
    exact h1.1 (isEndLike_iff_isEnd.mp h_end)
  | inr h_move =>
    obtain ⟨gr, hgr_mem, hgr_win⟩ := h_move
    unfold IsSpecial at h1
    cases h1.2 gr hgr_mem with
    | inl h_outcome_L =>
      rw [misereOutcome_L_iff_winsGoingFirst] at h_outcome_L
      exact hgr_win h_outcome_L.left
    | inr h_left_special =>
      obtain ⟨grl, hgrl_mem, hgrl_special⟩ := h_left_special
      have h4 := not_winsGoingFirst_right_of_isSpecial hgrl_special
      have h_left_wins_gr : WinsGoingFirst .left gr := winsGoingFirst_of_moves ⟨grl, hgrl_mem, h4⟩
      exact hgr_win h_left_wins_gr
      termination_by g
      decreasing_by form_wf

private lemma isSpecial_of_isPFree_not_winsGoingFirst_right_succ {g : GameForm} (h1 : IsPFree g)
    (h2 : ¬WinsGoingFirst .right (g + 1)) : IsSpecial g := by
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
      fun h_end => h2 (winsGoingFirst_of_isEnd h_end)

    -- If g were a Right end, then g+1 would also be a Right end (since 1 is a
    -- Right end)
    intro h_g_right_end
    apply h_g_plus_one_not_right_end
    rw [isEnd_def] at h_g_right_end ⊢
    rw [moves_add, rightMoves_one, Set.image_empty, Set.union_empty]
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
      apply winsGoingFirst_of_moves
      use gr + 1, h_gr_plus_one_mem
      simp only [Player.neg_right]
      exact h_left_not_wins

    -- 5. Since 1 is not a Left end, gr+1 is not a Left end, so there must
    -- exist some winning move for Left from gr+1
    -- 6. This winning move is either to gr (by playing on 1), or to some
    -- grl+1, where grl is a Left move of gr
    rw [winsGoingFirst_iff] at h_left_wins_gr_plus_one
    cases h_left_wins_gr_plus_one with
    | inl h_gr1_left_end =>
      have h_gr_is_left_move : gr ∈ moves .left (gr + 1) := by
        rw [moves_add, leftMoves_one]
        right; simp
      rw [h_gr1_left_end] at h_gr_is_left_move
      exfalso
      exact h_gr_is_left_move
    | inr h_left_has_winning_move =>
      obtain ⟨winning_move, h_winning_mem, h_winning_wins⟩ := h_left_has_winning_move

      rw [moves_add] at h_winning_mem
      rw [leftMoves_one] at h_winning_mem
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
          have h_gr_pfree : IsPFree gr := isPFree_of_mem_moves h1 h_gr_mem
          exact isPFree_of_mem_moves h_gr_pfree h_grl_mem

        -- 14. By induction, we must have grl.IsSpecial
        right
        use grl, h_grl_mem
        exact isSpecial_of_isPFree_not_winsGoingFirst_right_succ h_grl_pfree h_right_not_wins_grl_plus_one

      | inr h_winning_is_gr =>
        -- 7. Assume the winning move is to gr (by playing on 1)
        simp at h_winning_is_gr
        rw [← h_winning_is_gr] at h_winning_wins
        simp only [Player.neg_left] at h_winning_wins
        have h_right_not_wins_gr : ¬WinsGoingFirst .right gr := h_winning_wins

        -- 8. Since this is a winning move for Left (from gr+1), gr must have
        -- outcome L or P
        -- 9. Since g is p-free (h1), we know that gr is p-free
        have h_gr_pfree : IsPFree gr := isPFree_of_mem_moves h1 h_gr_mem

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
            rw [misereOutcome_R_iff_winsGoingFirst] at h_R
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

private theorem add_one_misereOutcome_ne_P_of_isPFree {g : GameForm} (h1 : IsPFree g)
    : MisereOutcome (g + 1) ≠ .P := by
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
    not_winsGoingFirst_of_misereOutcome_P h_outcome_P

  -- 2. By add_one_P_gives_special, g is special
  have h_g_special : IsSpecial g := isSpecial_of_isPFree_not_winsGoingFirst_right_succ h1 h_right_not_wins_g1

  -- 3. By SpecialImpliesWin, Right does not win g going first
  have h_right_not_wins_g : ¬WinsGoingFirst .right g := not_winsGoingFirst_right_of_isSpecial h_g_special

  -- 4. We will now show that Left wins g+1 going first.
  -- 5. Left can play on g+1 to g (by playing on 1)
  have h_g_is_left_move : g ∈ moves .left (g + 1) := by
    rw [moves_add, leftMoves_one]
    right; simp

  -- 6. Since Right doesn't win g going first, Left wins g+1 going first
  have h_left_wins_g_plus_one : WinsGoingFirst .left (g + 1) := by
    apply winsGoingFirst_of_moves
    use g, h_g_is_left_move, h_right_not_wins_g

  -- 7. But we assumed that g+1 had outcome P, which means Left does not win
  -- g+1 going first: this is a contradiction.
  have h_left_not_wins_g_plus_one : ¬WinsGoingFirst .left (g + 1) :=
    not_winsGoingFirst_of_misereOutcome_P h_outcome_P

  exact h_left_not_wins_g_plus_one h_left_wins_g_plus_one

theorem isPFree_add_one {g : GameForm} (h1 : IsPFree g) : IsPFree (g + 1) := by
  unfold IsPFree
  apply And.intro (add_one_misereOutcome_ne_P_of_isPFree h1)
  intro p
  simp only [moves_add, Set.mem_union, Set.mem_image]
  intro gp h2
  apply Or.elim h2 <;> intro h2
  · obtain ⟨k, h3, h4⟩ := h2
    rw [<-h4]
    exact isPFree_add_one (isPFree_of_mem_moves h1 h3)
  · cases p <;> simp only [Set.mem_empty_iff_false, Set.mem_singleton_iff, add_zero, exists_const,
                           exists_eq_left, false_and,
                           leftMoves_one, rightMoves_one] at h2
    rwa [<-h2]
termination_by g
decreasing_by form_wf

@[aesop safe apply]
theorem isPFree_add_natCast {g : GameForm} (h1 : IsPFree g) (n : ℕ) : IsPFree (g + n) := by
  induction n with
  | zero => rwa [Nat.cast_zero, add_zero]
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, <-add_assoc]
    exact isPFree_add_one ih

@[aesop safe apply]
theorem isPFree_natCast_add {g : GameForm} (h1 : IsPFree g) (n : ℕ) : IsPFree (n + g) := by
  rw [add_comm]
  exact isPFree_add_natCast h1 n

theorem isPFree_add_intCast {g : GameForm} (h1 : IsPFree g) (n : ℤ) : IsPFree (g + n) := by
  match n with
  | .ofNat m => exact isPFree_add_natCast h1 m
  | .negSucc m =>
    rw [Form.intCast_negSucc, <-ClosedUnderNeg.neg_iff (A := IsPFree), neg_add_rev, neg_neg, add_comm]
    exact isPFree_add_natCast h1.neg (m + 1)

namespace PFree

variable {A : GameForm → Prop} [PFree A]

theorem misereOutcome_ne_P_of_pfree {g : GameForm} (h1 : A g) : MisereOutcome g ≠ .P := by
  have h2 := PFree.pfree h1
  unfold IsPFree at h2
  exact h2.left

theorem isPFree_ofMoves {g gp : GameForm} {p : Player} (h1 : A g) (h2 : gp ∈ moves p g)
  : IsPFree gp := isPFree_of_mem_moves (PFree.pfree h1) h2

theorem exists_move_of_winsGoingFirst_not_isEnd {g : GameForm} {p : Player}
    (h1 : ¬IsEnd p g) (h2 : A g) (h3 : WinsGoingFirst p g) :
    (∃gr ∈ moves p g, WinsGoingFirst p gr) := by
  rw [winsGoingFirst_iff] at h3
  apply Or.elim h3 (fun h4 => False.elim (h1 (isEndLike_iff_isEnd.mp h4)))
  intro ⟨gr, h3, h4⟩
  use gr, h3
  by_cases h5 : WinsGoingFirst p gr
  · exact h5
  · have h6 : MisereOutcome gr = .P := misereOutcome_P_iff_winsGoingFirst'.mpr ⟨h5, h4⟩
    have h7 : MisereOutcome gr ≠ .P := misereOutcome_ne_P_of_pfree (isPFree_ofMoves h2 h3)
    exact False.elim (h7 h6)

mutual

private theorem not_winsGoingFirst_add_one_of_isPFree_not_winsGoingFirst_left {g : GameForm}
    (h0 : IsPFree g) (h1 : ¬WinsGoingFirst .left g) : ¬WinsGoingFirst .left (g + 1) := by
  intro h2
  rw [winsGoingFirst_iff] at h2
  obtain h2 | ⟨gl, h2, h3⟩ := h2
  · have h3 := (IsEndLike.add_iff.mp h2).right
    simp at h3
  · rw [Player.neg_left] at h3
    simp at h2
    obtain h2 | ⟨gll, h2, h4⟩ := h2
    · rw [h2] at h3
      have h4 := misereOutcome_P_iff_winsGoingFirst.mpr ⟨h3, h1⟩
      exact misereOutcome_ne_P_of_pfree h0 h4
    · rw [<-h4] at h3
      have h5 : IsPFree gll := isPFree_ofMoves h0 h2
      have h6 := not_winsGoingFirst_add_one_of_isPFree_not_winsGoingFirst_right h5 (by
        rw [winsGoingFirst_iff] at h1
        simp at h1
        obtain ⟨h1, h6⟩ := h1
        exact h6 gll h2)
      exact h3 h6
termination_by g
decreasing_by form_wf

private theorem not_winsGoingFirst_add_one_of_isPFree_not_winsGoingFirst_right {g : GameForm}
    (h0 : IsPFree g) (h1 : WinsGoingFirst .right g) : WinsGoingFirst .right (g + 1) := by
  rw [winsGoingFirst_iff] at h1
  obtain h1 | ⟨gr, h1, h2⟩ := h1
  · refine winsGoingFirst_add_of_isEnd (isEndLike_iff_isEnd.mp h1) ?_
    simp [isEnd_def]
  · refine winsGoingFirst_of_moves ⟨gr + 1, add_right_mem_moves_add h1 1, ?_⟩
    rw [Player.neg_right] at ⊢ h2
    exact not_winsGoingFirst_add_one_of_isPFree_not_winsGoingFirst_left (isPFree_ofMoves h0 h1) h2
termination_by g
decreasing_by form_wf

end

@[aesop safe apply]
theorem misereOutcome_add_one_R_of_misereOutcome_R {g : GameForm} (h0 : A g)
    (h1 : MisereOutcome g = .R) : MisereOutcome (g + 1) = .R := by
  simp only [misereOutcome_R_iff_winsGoingFirst]
  have ⟨h2, h3⟩ := misereOutcome_R_iff_winsGoingFirst.mp h1
  constructor
  · exact not_winsGoingFirst_add_one_of_isPFree_not_winsGoingFirst_right (PFree.pfree h0) h2
  · exact not_winsGoingFirst_add_one_of_isPFree_not_winsGoingFirst_left (PFree.pfree h0) h3

@[aesop safe apply]
theorem misereOutcome_add_natCast_R_of_misereOutcome_R {g : GameForm} (n : ℕ) (h0 : A g)
    (h1 : MisereOutcome g = .R) : MisereOutcome (g + n) = .R := by
  induction n with
  | zero => simp [h1]
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, <-add_assoc]
    exact misereOutcome_add_one_R_of_misereOutcome_R (isPFree_add_natCast (PFree.pfree h0) k) ih

mutual

private theorem not_winsGoingFirst_sub_one_of_not_winsGoingFirst_right {g : GameForm}
    (h0 : IsPFree g) (h1 : ¬WinsGoingFirst .right g) : ¬WinsGoingFirst .right (g + (-1)) := by
  intro h2
  rw [winsGoingFirst_iff] at h2
  obtain h2 | ⟨gl, h2, h3⟩ := h2
  · have h3 := (IsEnd.add_iff.mp (isEndLike_iff_isEnd.mp h2)).right
    simp [isEnd_def] at h3
  · rw [Player.neg_right] at h3
    simp at h2
    obtain h2 | ⟨gll, h2, h4⟩ := h2
    · rw [h2] at h3
      have h4 := misereOutcome_P_iff_winsGoingFirst.mpr ⟨h1, h3⟩
      exact misereOutcome_ne_P_of_pfree h0 h4
    · rw [<-h4] at h3
      have h5 : IsPFree gll := isPFree_of_mem_moves h0 h2
      have h6 := not_winsGoingFirst_sub_one_of_not_winsGoingFirst_left h5 (by
        rw [winsGoingFirst_iff] at h1
        simp at h1
        obtain ⟨h1, h6⟩ := h1
        exact h6 gll h2)
      exact h3 h6
termination_by g
decreasing_by form_wf

private theorem not_winsGoingFirst_sub_one_of_not_winsGoingFirst_left {g : GameForm}
    (h0 : IsPFree g) (h1 : WinsGoingFirst .left g) : WinsGoingFirst .left (g + (-1)) := by
  rw [winsGoingFirst_iff] at h1
  obtain h1 | ⟨gr, h1, h2⟩ := h1
  · refine winsGoingFirst_add_of_isEnd (isEndLike_iff_isEnd.mp h1) ?_
    simp [isEnd_def]
  · refine winsGoingFirst_of_moves ⟨gr + (-1), add_right_mem_moves_add h1 (-1), ?_⟩
    rw [Player.neg_left] at ⊢ h2
    exact not_winsGoingFirst_sub_one_of_not_winsGoingFirst_right (isPFree_of_mem_moves h0 h1) h2
termination_by g
decreasing_by form_wf

end

theorem misereOutcome_sub_one_L_of_misereOutcome_L {g : GameForm} (h0 : A g)
    (h1 : MisereOutcome g = .L) : MisereOutcome (g + (-1)) = .L := by
  simp only [misereOutcome_L_iff_winsGoingFirst]
  have ⟨h2, h3⟩ := misereOutcome_L_iff_winsGoingFirst.mp h1
  constructor
  · exact not_winsGoingFirst_sub_one_of_not_winsGoingFirst_left (PFree.pfree h0) h2
  · exact not_winsGoingFirst_sub_one_of_not_winsGoingFirst_right (PFree.pfree h0) h3

theorem misereOutcome_sub_natCast_L_of_misereOutcome_L {g : GameForm} (n : ℕ) (h0 : A g)
    (h1 : MisereOutcome g = .L) : MisereOutcome (g + (-n)) = .L := by
  induction n with
  | zero => simp [h1]
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, neg_add_rev, add_comm (-1), <-add_assoc]
    refine misereOutcome_sub_one_L_of_misereOutcome_L (A := IsPFree) ?_ ih
    rw [<-ClosedUnderNeg.neg_iff (A := IsPFree), neg_add_rev, neg_neg, add_comm]
    exact isPFree_add_natCast (ClosedUnderNeg.neg_iff.mpr (PFree.pfree h0)) k

theorem misereOutcome_of_isEnd {g : GameForm} {p : Player} (h1 : A g) (h2 : IsEnd p g)
    : MisereOutcome g = .N ∨ MisereOutcome g = Outcome.ofPlayers p p := by
  have h4 :=
    miserePlayerOutcome_eq_iff_winsGoingFirst.mpr (winsGoingFirst_of_isEnd h2)
  cases h5 : MisereOutcome g
  · cases p
    · exact Or.inr rfl
    · absurd h4
      simp [(misereOutcome_L_iff_miserePlayerOutcome.mp h5).right]
  · exact Or.inl rfl
  · absurd h5
    exact misereOutcome_ne_P_of_pfree h1
  · cases p
    · absurd h4
      simp [(misereOutcome_R_iff_miserePlayerOutcome.mp h5).left]
    · exact Or.inr rfl

theorem misereOutcome_of_isEnd_left {g : GameForm} (h1 : A g) (h2 : IsEnd .left g)
    : MisereOutcome g = .N ∨ MisereOutcome g = .L := misereOutcome_of_isEnd h1 h2

theorem misereOutcome_of_isEnd_right {g : GameForm} (h1 : A g) (h2 : IsEnd .right g)
    : MisereOutcome g = .N ∨ MisereOutcome g = .R := misereOutcome_of_isEnd h1 h2

end PFree
