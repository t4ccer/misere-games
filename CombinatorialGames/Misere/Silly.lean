/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.GameForm
public import CombinatorialGames.Form.Misere.Outcome
public import CombinatorialGames.Misere.PFree

universe u

public section

namespace GameForm

open Form
open Form.Misere.Outcome

/--
Intuitively a position is solved for a given player if they win no matter what they do
-/
def IsSolved (p : Player) (g : GameForm) : Prop :=
  (IsOption 0 g → 0 ∉ moves p g)
  ∧ (g ≠ 0 → ¬IsEnd (-p) g)
  ∧ (∀ gp, IsOption gp g → IsSolved p gp)
termination_by g
decreasing_by form_wf

theorem isSolved_zero_not_mem {p : Player} {g : GameForm}
    (h_isSolved : IsSolved p g) (h_isOption : IsOption 0 g) :
    0 ∉ moves p g := by
  unfold IsSolved at h_isSolved
  exact h_isSolved.left h_isOption

theorem isSolved_zero_mem {p : Player} {g : GameForm}
    (h_isSolved : IsSolved p g) (h_isOption : IsOption 0 g) :
    0 ∈ moves (-p) g := by
  unfold IsSolved at h_isSolved
  have h_not_mem := h_isSolved.left h_isOption
  simp only [isOption_iff_mem_union, Set.mem_union] at h_isOption
  cases p
  · exact h_isOption.resolve_left h_not_mem
  · exact h_isOption.resolve_right h_not_mem

theorem isSolved_not_isEnd {p : Player} {g : GameForm}
    (h_isSolved : IsSolved p g) (h_ne_zero : g ≠ 0) : ¬IsEnd (-p) g := by
  unfold IsSolved at h_isSolved
  exact h_isSolved.right.left h_ne_zero

theorem isSolved_of_isOption {g gp : GameForm} {p : Player} (h1 : IsSolved p g) (h2 : IsOption gp g) :
    IsSolved p gp := by
  unfold IsSolved at h1
  exact h1.right.right gp h2

theorem isSolved_of_mem_moves {p : Player} {g g' : GameForm} {q : Player}
    (h : IsSolved p g) (hm : g' ∈ moves q g) : IsSolved p g' :=
  isSolved_of_isOption h (IsOption.of_mem_moves hm)

----------------------------------------------------------------------------------------------------

private theorem isSolved_neg {p : Player} {g : GameForm} (h_isSolved : IsSolved p g) :
    IsSolved (-p) (-g) := by
  unfold IsSolved
  refine ⟨?_, ?_, ?_⟩
  · intro h_isOption; rw [isOption_zero_neg_iff] at h_isOption
    simp only [moves_neg, neg_neg, Set.mem_neg, neg_zero]
    exact isSolved_zero_not_mem h_isSolved h_isOption
  · intro h_ne_zero; rw [neg_ne_zero] at h_ne_zero
    rw [neg_neg, IsEnd.neg_iff_neg]
    exact isSolved_not_isEnd h_isSolved h_ne_zero
  · intro gp h_isOption
    rw [isOption_neg] at h_isOption
    have h_isSolved_gp := isSolved_of_isOption h_isSolved h_isOption
    rw [<-neg_neg p] at h_isSolved_gp
    have h_isSolved_neg_gp := isSolved_neg h_isSolved_gp
    rwa [neg_neg, neg_neg] at h_isSolved_neg_gp
termination_by birthday g
decreasing_by
  -- gameform_birthday
  rw [isOption_neg] at h_isOption
  exact birthday_lt_of_isOption h_isOption

@[simp]
theorem isSolved_neg_iff {p : Player} {g : GameForm} : IsSolved (-p) (-g) ↔ IsSolved p g := by
  constructor
  · intro h_isSolved
    have h_isSolved_neg := isSolved_neg h_isSolved
    rwa [neg_neg, neg_neg] at h_isSolved_neg
  · exact isSolved_neg

theorem isSolved_winsGoingFirst {p : Player} {g : GameForm} (h_isSolved : IsSolved p g) :
    WinsGoingFirst p g := by
  by_cases h_isEnd : IsEnd p g
  · -- If G is an end then p wins instantly
    exact winsGoingFirst_of_isEnd h_isEnd
  · -- Otherwise there exist some G^P which is also solved for p
    have ⟨gp, h_gp_mem⟩ := not_isEnd_exists_move h_isEnd
    have h_gp_isSolved := (isSolved_of_mem_moves h_isSolved h_gp_mem)
    -- But G is solved for p so G^P ≠ 0
    have h_gp_ne_zero : gp ≠ 0 := by
      intro h
      subst h
      have zero_not_mem:= isSolved_zero_not_mem h_isSolved (IsOption.of_mem_moves h_gp_mem)
      exact zero_not_mem h_gp_mem
    apply winsGoingFirst_of_moves
    use gp, h_gp_mem
    rw [not_winsGoingFirst_iff]
    -- Now since G^P ≠ 0 it cannot be a -p end since G is solved for P and every subposition of
    -- G^P is winning if p goes first by induction.
    apply And.intro (isEndLike_iff_isEnd.not.mpr (isSolved_not_isEnd h_gp_isSolved h_gp_ne_zero))
    intro gpp h_gpp_mem
    rw [neg_neg]
    have h_gpp_isSolved := isSolved_of_mem_moves h_gp_isSolved h_gpp_mem
    exact isSolved_winsGoingFirst h_gpp_isSolved
termination_by g
decreasing_by form_wf

theorem isSolved_ne_zero_misereOutcome {p : Player} {g : GameForm}
    (h_isSolved : IsSolved p g) (h_ne_zero : g ≠ 0) :
    MisereOutcome g = Outcome.ofPlayer p := by
  rw [misereOutcome_eq_player_iff]
  apply And.intro (isSolved_winsGoingFirst h_isSolved)
  rw [not_winsGoingFirst_iff, isEndLike_iff_isEnd, neg_neg]
  apply And.intro (isSolved_not_isEnd h_isSolved h_ne_zero)
  intro gp h_gp_mem
  exact isSolved_winsGoingFirst (isSolved_of_mem_moves h_isSolved h_gp_mem)

/--
Sum of two solved games is solved
-/
theorem isSolved_add {p : Player} {g h : GameForm}
    (h_isSolved_g : IsSolved p g) (h_isSolved_h : IsSolved p h) : IsSolved p (g + h) := by
  unfold IsSolved
  refine ⟨?_, ?_, ?_⟩
  · intro h_zero_gh
    apply Or.elim (isOption_zero_add_iff.mp h_zero_gh)
    · intro ⟨h_zero_g, h_g_zero⟩
      by_contra h_zero_mem_gh
      have h_zero_mem_g := isSolved_zero_mem h_isSolved_g h_zero_g
      rw [h_g_zero, add_zero] at h_zero_mem_gh
      exact isSolved_zero_not_mem h_isSolved_g h_zero_g h_zero_mem_gh
    · intro ⟨h_zero_h, h_h_zero⟩
      by_contra h_zero_mem_gh
      have h_zero_mem_h := isSolved_zero_mem h_isSolved_h h_zero_h
      rw [h_h_zero, zero_add] at h_zero_mem_gh
      exact isSolved_zero_not_mem h_isSolved_h h_zero_h h_zero_mem_gh
  · intro h_gh_ne_zero
    have h_not_gh_zero := (add_eq_zero_iff (G := GameForm) (x := g) (y := h)).not.mp h_gh_ne_zero
    rw [not_and_or] at h_not_gh_zero
    apply Or.elim h_not_gh_zero
    · intro h_g_ne_zero
      exact not_isEnd_add_left (isSolved_not_isEnd h_isSolved_g h_g_ne_zero)
    · intro h_h_ne_zero
      exact not_isEnd_add_right (isSolved_not_isEnd h_isSolved_h h_h_ne_zero)
  · intro ghp h_isOption_ghp
    simp only [IsOption.iff_mem_union, moves_add, Set.mem_union, Set.mem_image] at h_isOption_ghp
    obtain (⟨x, h_x_mem, h_xh⟩ | ⟨x, h_x_mem, h_gx⟩) | ⟨x, h_x_mem, h_xh⟩ | ⟨x, h_x_mem, h_gx⟩ := h_isOption_ghp
    · subst h_xh
      exact isSolved_add (isSolved_of_mem_moves h_isSolved_g h_x_mem) h_isSolved_h
    · subst h_gx
      exact isSolved_add h_isSolved_g (isSolved_of_mem_moves h_isSolved_h h_x_mem)
    · subst h_xh
      exact isSolved_add (isSolved_of_mem_moves h_isSolved_g h_x_mem) h_isSolved_h
    · subst h_gx
      exact isSolved_add h_isSolved_g (isSolved_of_mem_moves h_isSolved_h h_x_mem)
termination_by (g, h)
decreasing_by form_wf

theorem not_isSolved_add_left {p : Player} {g h : GameForm}
    (hg : ¬IsSolved p g) : ¬IsSolved p (g + h) := by
  by_cases h_zero : h = 0
  · rwa [h_zero, add_zero]
  · have ⟨q, hq⟩ := ne_zero_not_end h_zero
    have ⟨h1, hh1⟩ := not_isEnd_exists_move hq
    intro h_solved
    exact not_isSolved_add_left hg (isSolved_of_mem_moves h_solved (add_left_mem_moves_add hh1 g))
termination_by h
decreasing_by form_wf

theorem not_isSolved_add_right {p : Player} {g h : GameForm}
    (hh : ¬IsSolved p h) : ¬IsSolved p (g + h) := by
  rw [add_comm];
  exact not_isSolved_add_left hh

theorem isSolved_add_iff {p : Player} {g h : GameForm} :
    IsSolved p g ∧ IsSolved p h ↔ IsSolved p (g + h) := by
  constructor
  · intro ⟨h_isSolved_g, h_isSolved_h⟩
    exact isSolved_add h_isSolved_g h_isSolved_h
  · intro h_isSolved_gh
    by_contra h
    simp only [not_and_or] at h
    obtain h_isSolved_g | h_isSolved_h := h
    · exact not_isSolved_add_left h_isSolved_g h_isSolved_gh
    · exact not_isSolved_add_right h_isSolved_h h_isSolved_gh

@[simp]
theorem isSolved_zero (p : Player) : IsSolved p 0 := by
  unfold IsSolved
  simp

@[simp]
theorem isSolved_right_natCast (n : ℕ) : IsSolved .right (n : GameForm) := by
  induction n with
  | zero => exact isSolved_zero .right
  | succ k ih => unfold IsSolved; simpa [IsOption.iff_mem_union] using ih

@[simp]
theorem isSolved_right_one : IsSolved .right 1 := by
  rw [←Nat.cast_one]
  exact isSolved_right_natCast 1

/--
Zero is the only game solved for both players
-/
theorem isSolved_iff_zero {g : GameForm} : (IsSolved .left g ∧ IsSolved .right g) ↔ g = 0 := by
  constructor
  · intro ⟨h_isSolved_left, h_isSolved_right⟩
    -- Suppose for the sake of contradiction that G ≠ 0
    by_contra h_ne_zero
    -- Then since G is solved for Left, G is not a Right end so there exists some G^R
    have ⟨gr, h_gr_mem_r⟩ := not_isEnd_exists_move (isSolved_not_isEnd h_isSolved_right h_ne_zero)
    -- Since G is solved for both players, G^R is also solved by both players so by induction G^R = 0
    have h_gr := isSolved_iff_zero.mp
                 ⟨ isSolved_of_isOption h_isSolved_left (IsOption.of_mem_moves h_gr_mem_r)
                 , isSolved_of_isOption h_isSolved_right (IsOption.of_mem_moves h_gr_mem_r)⟩
    subst h_gr
    -- But G is solved for Left so 0 cannot be a Left option of G
    have h_gr_not_mem_l := isSolved_zero_not_mem h_isSolved_right (IsOption.of_mem_moves h_gr_mem_r)

    -- Similarly since G is solved for Right, G is not a Left end so there exists some G^L
    have ⟨gl, h_gl_mem_l⟩ := not_isEnd_exists_move (isSolved_not_isEnd h_isSolved_left h_ne_zero)
    -- Since G is solved for both players, G^L is also solved by both players so by induction G^L = 0
    have h_gl := isSolved_iff_zero.mp
                 ⟨ isSolved_of_isOption h_isSolved_left (IsOption.of_mem_moves h_gl_mem_l)
                 , isSolved_of_isOption h_isSolved_right (IsOption.of_mem_moves h_gl_mem_l)⟩
    subst h_gl
    -- Which is a contradiction since 0 cannot be a Left option of G
    exact h_gr_not_mem_l h_gl_mem_l
  · intro h_eq_zero
    rw [h_eq_zero]
    exact ⟨isSolved_zero .left, isSolved_zero .right⟩
termination_by g
decreasing_by form_wf

@[simp]
theorem isSolved_right_intCast_iff (k : ℤ) : IsSolved .right (k : GameForm) ↔ 0 ≤ k := by
  constructor
  · intro h_isSolved_left
    match k with
    | .ofNat n => exact Int.zero_le_ofNat n
    | .negSucc n =>
      by_contra h_le
      rw [Form.intCast_negSucc, <-Player.neg_left, isSolved_neg_iff] at h_isSolved_left
      have h_isSolved_right := isSolved_add (isSolved_right_natCast n) isSolved_right_one
      have h_absurd := isSolved_iff_zero.mp ⟨h_isSolved_left, h_isSolved_right⟩
      simp only [add_eq_zero_iff, Nat.cast_eq_zero, one_ne_zero, and_false] at h_absurd
  · intro h_le
    match k with
    | .ofNat n => simp only [Int.ofNat_eq_natCast, Form.intCast_nat, isSolved_right_natCast]
    | .negSucc _ => simp only [Int.negSucc_not_nonneg] at h_le

@[simp]
theorem isSolved_left_intCast_iff (k : ℤ) : IsSolved .left (k : GameForm) ↔ k ≤ 0 := by
  rw [<-isSolved_neg_iff, Player.neg_left, <-Form.intCast_neg, isSolved_right_intCast_iff]
  exact Int.neg_nonneg

/--
Stride measures exactly how many moves away each player is from a solved position

Stride is not well defined for all game forms
-/
def HasStride (p : Player) (g : GameForm) (n : ℕ) : Prop :=
  match n with
  | 0 => IsSolved p g
  | n + 1 =>
    ¬IsSolved p g
    ∧ (∀ g' ∈ moves p g, ∃ k, n ≤ k ∧ HasStride p g' k)
    -- NOTE: We say that the opponent's stride in our "best" move has a maximum stride rather than
    -- saying that stride did not change to prevent a loopy definition, these are equivalent
    ∧ (∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n
        ∧ ∀ g'' ∈ moves p g, ∀ m, HasStride (-p) g'' m → ∃ k, m ≤ k ∧ HasStride (-p) g' k)
    ∧ (∀ g' ∈ moves (-p) g, ∃ k, k ≤ n + 1 ∧ HasStride p g' k)
    ∧ (moves (-p) g ≠ ∅ → ∃ g', ∃ (_ : g' ∈ moves (-p) g), HasStride p g' (n + 1))
termination_by birthday g
decreasing_by all_goals exact birthday_lt_of_mem_moves (by assumption)

/--
Stride equals zero if game is solved
-/
@[simp]
theorem hasStride_zero_iff {p : Player} {g : GameForm} :
    HasStride p g 0 ↔ IsSolved p g := by
  constructor
  · intro h; unfold HasStride at h; exact h
  · intro h; unfold HasStride; exact h

/--
Game is solved if its stride equals zero
-/
theorem hasStride_isSolved_iff_zero {p : Player} {g : GameForm} {n : ℕ}
    (h_hasStride : HasStride p g n) : IsSolved p g ↔ n = 0 := by
  unfold HasStride at h_hasStride
  constructor
  · intro h_isSolved
    match n with
    | .zero => rfl
    | .succ k => exact absurd h_isSolved h_hasStride.left
  · intro h_zero; subst h_zero; exact h_hasStride

theorem hasStride_succ_iff {p : Player} {g : GameForm} {n : ℕ} :
    HasStride p g (n + 1) ↔
    ¬IsSolved p g
    ∧ (∀ g' ∈ moves p g, ∃ k, n ≤ k ∧ HasStride p g' k)
    ∧ (∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n
        ∧ ∀ g'' ∈ moves p g, ∀ m, HasStride (-p) g'' m → ∃ k, m ≤ k ∧ HasStride (-p) g' k)
    ∧ (∀ g' ∈ moves (-p) g, ∃ k, k ≤ n + 1 ∧ HasStride p g' k)
    ∧ (moves (-p) g ≠ ∅ → ∃ g', ∃ (_ : g' ∈ moves (-p) g), HasStride p g' (n + 1)) := by
  constructor
  · intro h; unfold HasStride at h; exact h
  · intro h; unfold HasStride; exact h

/--
If the stride of $G$ is not zero then every response lowers the stride by at most one
-/
theorem hasStride_succ_support {p : Player} {g : GameForm} {n : ℕ}
    (h : HasStride p g (n + 1)) (g' : GameForm) (hg' : g' ∈ moves p g) :
    ∃ k, n ≤ k ∧ HasStride p g' k :=
  (hasStride_succ_iff.mp h).2.1 g' hg'

/--
If the stride of $G$ is not zero then there exist some response to stride lower by one
-/
theorem hasStride_succ_exists_best {p : Player} {g : GameForm} {n : ℕ}
    (h : HasStride p g (n + 1)) :
    ∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n
        ∧ ∀ g'' ∈ moves p g, ∀ m, HasStride (-p) g'' m → ∃ k, m ≤ k ∧ HasStride (-p) g' k :=
  (hasStride_succ_iff.mp h).2.2.1

/--
If the stride of $G$ is not zero then every opponent move preserves the stride
-/
theorem hasStride_succ_support_neg {p : Player} {g : GameForm} {n : ℕ}
    (h : HasStride p g (n + 1)) (g' : GameForm) (hg' : g' ∈ moves (-p) g) :
    ∃ k, k ≤ n + 1 ∧ HasStride p g' k :=
  (hasStride_succ_iff.mp h).2.2.2.1 g' hg'

/--
Some opponent move preserves stride
-/
theorem hasStride_succ_exists_preserve_neg {p : Player} {g : GameForm} {n : ℕ}
    (h : HasStride p g (n + 1)) (h_ne : moves (-p) g ≠ ∅) :
    ∃ g', ∃ (_ : g' ∈ moves (-p) g), HasStride p g' (n + 1) :=
  (hasStride_succ_iff.mp h).2.2.2.2 h_ne

theorem hasStride_succ_not_isEnd {p : Player} {g : GameForm} {n : ℕ}
    (h : HasStride p g (n + 1)) : ¬IsEnd p g := by
  have ⟨_, h_mem, _, _⟩ := hasStride_succ_exists_best h
  exact not_isEnd_of_mem_moves h_mem

/--
If a game has stride then the value is unique

This is a workaround for not defining stride as a function to `option ℕ`
-/
theorem hasStride_unique {p : Player} {g : GameForm} {n k : ℕ}
    (h_n : HasStride p g n) (h_k : HasStride p g k) : n = k := by
  match n, k with
  | 0, 0 => rfl
  | 0, .succ _ => have := (hasStride_isSolved_iff_zero h_k).mp (hasStride_zero_iff.mp h_n); omega
  | .succ _, 0 => have := (hasStride_isSolved_iff_zero h_n).mp (hasStride_zero_iff.mp h_k); omega
  | .succ n, .succ k =>
    congr 1
    have ⟨g1, hg1_mem, hg1_stride, _⟩ := hasStride_succ_exists_best h_n
    have ⟨j, hkj, hj_stride⟩ := hasStride_succ_support h_k g1 hg1_mem
    have h_nj : n = j := hasStride_unique hg1_stride hj_stride
    subst h_nj
    have ⟨g2, hg2_mem, hg2_stride, _⟩ := hasStride_succ_exists_best h_k
    have ⟨j', hnj', hj'_stride⟩ := hasStride_succ_support h_n g2 hg2_mem
    have h_kj' : k = j' := hasStride_unique hg2_stride hj'_stride
    subst h_kj'
    exact Nat.le_antisymm hnj' hkj
termination_by birthday g
decreasing_by all_goals exact birthday_lt_of_mem_moves (by assumption)

/--
The good move preserves (-p)-stride: if HasStride p g (n+1) and HasStride (-p) g r,
then the good p-move has (-p)-stride exactly r.
-/
theorem hasStride_good_move_neg_stride {p : Player} {g : GameForm} {n r : ℕ}
    (h : HasStride p g (n + 1))
    (h_r : HasStride (-p) g r) :
    ∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n ∧ HasStride (-p) g' r := by
  have ⟨g1, hg1_mem, hg1_stride_p, hg1_max⟩ := hasStride_succ_exists_best h
  refine ⟨g1, hg1_mem, hg1_stride_p, ?_⟩
  match r with
  | 0 =>
    exact hasStride_zero_iff.mpr (isSolved_of_mem_moves (hasStride_zero_iff.mp h_r) hg1_mem)
  | .succ r' =>
    have hg1_bound := hasStride_succ_support_neg h_r g1 (by rw [neg_neg]; exact hg1_mem)
    obtain ⟨k1, hk1_le, hk1_stride⟩ := hg1_bound
    have h_ne : moves p g ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨g1, hg1_mem⟩
    have hD := hasStride_succ_exists_preserve_neg h_r (by rw [neg_neg]; exact h_ne)
    obtain ⟨g2, hg2_mem, hg2_stride⟩ := hD
    rw [neg_neg] at hg2_mem
    have ⟨k2, hk2_ge, hk2_stride⟩ := hg1_max g2 hg2_mem (r' + 1) hg2_stride
    have h_eq : k1 = k2 := hasStride_unique hk1_stride hk2_stride
    rw [h_eq] at hk1_le
    have : k2 = r' + 1 := Nat.le_antisymm hk1_le hk2_ge
    rw [this] at hk2_stride
    exact hk2_stride

/--
Opponent moves have stride ≤ n
-/
theorem hasStride_of_mem_moves_neg {p : Player} {g g' : GameForm} {n : ℕ}
    (hg : HasStride p g n) (hm : g' ∈ moves (-p) g) : ∃ k, k ≤ n ∧ HasStride p g' k := by
  match n with
  | 0 => exact ⟨0, le_refl _, hasStride_zero_iff.mpr (isSolved_of_mem_moves (hasStride_zero_iff.mp hg) hm)⟩
  | .succ n' =>
    exact hasStride_succ_support_neg hg g' hm

/--
A variant of `hasStride_succ_iff` that simplifies condition B' when we know the (-p)-stride.
Instead of requiring the good move to have the max (-p)-stride among all p-moves,
we simply require the good move to preserve the (-p)-stride exactly.
-/
theorem hasStride_succ_iff' {p : Player} {g : GameForm} {n m : ℕ}
    (h_hasStride_m : HasStride (-p) g m) :
    HasStride p g (n + 1) ↔
    ¬IsSolved p g
    ∧ (∀ g' ∈ moves p g, ∃ k, n ≤ k ∧ HasStride p g' k)
    ∧ (∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n ∧ HasStride (-p) g' m)
    ∧ (∀ g' ∈ moves (-p) g, ∃ k, k ≤ n + 1 ∧ HasStride p g' k)
    ∧ (moves (-p) g ≠ ∅ → ∃ g', ∃ (_ : g' ∈ moves (-p) g), HasStride p g' (n + 1)) := by
  rw [hasStride_succ_iff]
  constructor <;> intro h <;> rcases h with ⟨h₁, h₂, h₃, h₄, h₅⟩
  · exact ⟨h₁, h₂, hasStride_good_move_neg_stride (hasStride_succ_iff.mpr ⟨h₁, h₂, h₃, h₄, h₅⟩) h_hasStride_m, h₄, h₅⟩
  · obtain ⟨g', hg', hg₁, hg₂⟩ := h₃
    have h_bound : ∀ g'' ∈ moves p g, ∀ m', HasStride (-p) g'' m' → m' ≤ m := by
      intro g'' hg'' m' hm'
      obtain ⟨k, hk, hk_s⟩ := hasStride_of_mem_moves_neg h_hasStride_m (show g'' ∈ moves (-(-p)) g by rwa [neg_neg])
      exact hasStride_unique hm' hk_s ▸ hk
    exact ⟨h₁, h₂, ⟨g', hg', hg₁, fun g'' hg'' m' hm' => ⟨m, h_bound g'' hg'' m' hm', hg₂⟩⟩, h₄, h₅⟩

/--
Variant of `hasStride_succ_exists_best` with known opponent stride
-/
theorem hasStride_succ_exists_best' {p : Player} {g : GameForm} {n m : ℕ}
    (h_n : HasStride p g (n + 1)) (h_m : HasStride (-p) g m) :
    ∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n ∧ HasStride (-p) g' m :=
  ((hasStride_succ_iff' h_m).mp h_n).2.2.1

theorem hasStride_of_mem_moves {p : Player} {g g' : GameForm} {n : ℕ}
    (hg : HasStride p g n) (hm : g' ∈ moves p g) :
    ∃ j, n - 1 ≤ j ∧ HasStride p g' j := by
  match n with
  | 0 => exact ⟨0, Nat.zero_le _, hasStride_zero_iff.mpr (isSolved_of_mem_moves (hasStride_zero_iff.mp hg) hm)⟩
  | .succ n =>
    have ⟨j, hj, hjs⟩ := hasStride_succ_support hg g' hm
    exact ⟨j, by simpa only [Nat.succ_eq_add_one, add_tsub_cancel_right] using hj, hjs⟩

/--
Stride of sum is the sum of strides.
-/
theorem hasStride_add {p : Player} {g h : GameForm} {n k m l : ℕ}
    (h_gp : HasStride p g n) (h_hp : HasStride p h k)
    (h_gn : HasStride (-p) g m) (h_hn : HasStride (-p) h l) :
    HasStride p (g + h) (n + k) := by
  match n, k with
  | 0, 0 =>
    exact hasStride_zero_iff.mpr (isSolved_add (hasStride_zero_iff.mp h_gp) (hasStride_zero_iff.mp h_hp))
  | n' + 1, k =>
    rw [show n' + 1 + k = (n' + k) + 1 by omega, hasStride_succ_iff]
    have ⟨g₁, hg1_mem, hg1_p, hg1_neg⟩ := hasStride_good_move_neg_stride h_gp h_gn
    have h_neg_g1h : HasStride (-p) (g₁ + h) (m + l) :=
      hasStride_add hg1_neg h_hn (by rwa [neg_neg]) (by rwa [neg_neg])
    refine ⟨not_isSolved_add_left (hasStride_succ_iff.mp h_gp).1, ?_, ?_, ?_, ?_⟩
    · intro g' hg'
      rw [moves_add] at hg'
      simp only [Set.mem_union, Set.mem_image] at hg'
      obtain ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ := hg'
      · have ⟨j, hj, hj_s⟩ := hasStride_of_mem_moves h_gp hx
        have ⟨mx, hmx, hmx_s⟩ := hasStride_of_mem_moves_neg h_gn (show x ∈ moves (-(-p)) g by rwa [neg_neg])
        exact ⟨j + k, by omega, hasStride_add hj_s h_hp hmx_s h_hn⟩
      · have ⟨j, hj, hj_s⟩ := hasStride_of_mem_moves h_hp hx
        have ⟨lx, hlx, hlx_s⟩ := hasStride_of_mem_moves_neg h_hn (show x ∈ moves (-(-p)) h by rwa [neg_neg])
        exact ⟨(n' + 1) + j, by omega, hasStride_add h_gp hj_s h_gn hlx_s⟩
    · refine ⟨g₁ + h, add_right_mem_moves_add hg1_mem h, hasStride_add hg1_p h_hp hg1_neg h_hn, ?_⟩
      intro g'' hg'' m' hm'
      rw [moves_add] at hg''
      simp only [Set.mem_union, Set.mem_image] at hg''
      obtain ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ := hg''
      · have ⟨mx, hmx, hmx_s⟩ := hasStride_of_mem_moves_neg h_gn (show x ∈ moves (-(-p)) g by rwa [neg_neg])
        have ⟨jx, _, hjx_s⟩ := hasStride_of_mem_moves h_gp hx
        have h_neg_xh : HasStride (-p) (x + h) (mx + l) :=
          hasStride_add hmx_s h_hn (by rwa [neg_neg]) (by rwa [neg_neg])
        rw [hasStride_unique hm' h_neg_xh]
        exact ⟨m + l, by omega, h_neg_g1h⟩
      · have ⟨lx, hlx, hlx_s⟩ := hasStride_of_mem_moves_neg h_hn (show x ∈ moves (-(-p)) h by rwa [neg_neg])
        have ⟨jx, _, hjx_s⟩ := hasStride_of_mem_moves h_hp hx
        have h_neg_gx : HasStride (-p) (g + x) (m + lx) :=
          hasStride_add h_gn hlx_s (by rwa [neg_neg]) (by rwa [neg_neg])
        rw [hasStride_unique hm' h_neg_gx]
        exact ⟨m + l, by omega, h_neg_g1h⟩
    · intro g' hg'
      rw [moves_add] at hg'
      simp only [Set.mem_union, Set.mem_image] at hg'
      obtain ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ := hg'
      · have ⟨j, hj, hj_s⟩ := hasStride_of_mem_moves_neg h_gp hx
        have ⟨mx, _, hmx_s⟩ := hasStride_of_mem_moves h_gn hx
        exact ⟨j + k, by omega, hasStride_add hj_s h_hp hmx_s h_hn⟩
      · have ⟨j, hj, hj_s⟩ := hasStride_of_mem_moves_neg h_hp hx
        have ⟨lx, _, hlx_s⟩ := hasStride_of_mem_moves h_hn hx
        exact ⟨(n' + 1) + j, by omega, hasStride_add h_gp hj_s h_gn hlx_s⟩
    · intro h_ne
      rw [moves_add] at h_ne
      rw [Set.nonempty_iff_ne_empty.symm] at h_ne
      simp only [Set.Nonempty, Set.mem_union, Set.mem_image] at h_ne
      obtain ⟨_, ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩⟩ := h_ne
      · have h_ne_g : moves (-p) g ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨x, hx⟩
        have ⟨g', hg'_mem, hg'_s⟩ := hasStride_succ_exists_preserve_neg h_gp h_ne_g
        have ⟨mg', _, hmg'_s⟩ := hasStride_of_mem_moves h_gn hg'_mem
        have := hasStride_add hg'_s h_hp hmg'_s h_hn
        rw [show (n' + 1) + k = (n' + k) + 1 by omega] at this
        exact ⟨g' + h, add_right_mem_moves_add hg'_mem h, this⟩
      · match k with
        | 0 =>
          have hx_solved := isSolved_of_mem_moves (hasStride_zero_iff.mp h_hp) hx
          have hx_s := hasStride_zero_iff.mpr hx_solved
          have ⟨lx, _, hlx_s⟩ := hasStride_of_mem_moves h_hn hx
          have := hasStride_add h_gp hx_s h_gn hlx_s
          rw [show (n' + 1) + 0 = (n' + 0) + 1 by omega] at this
          exact ⟨g + x, add_left_mem_moves_add hx g, this⟩
        | k' + 1 =>
          have h_ne_h : moves (-p) h ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨x, hx⟩
          have ⟨h', hh'_mem, hh'_s⟩ := hasStride_succ_exists_preserve_neg h_hp h_ne_h
          have ⟨lh', _, hlh'_s⟩ := hasStride_of_mem_moves h_hn hh'_mem
          have := hasStride_add h_gp hh'_s h_gn hlh'_s
          rw [show (n' + 1) + (k' + 1) = (n' + (k' + 1)) + 1 by omega] at this
          exact ⟨g + h', add_left_mem_moves_add hh'_mem g, this⟩
  | 0, k' + 1 =>
    rw [show 0 + (k' + 1) = k' + 1 by omega, hasStride_succ_iff]
    have ⟨h₁, hh1_mem, hh1_p, hh1_neg⟩ := hasStride_good_move_neg_stride h_hp h_hn
    have h_neg_gh1 : HasStride (-p) (g + h₁) (m + l) :=
      hasStride_add h_gn hh1_neg (by rwa [neg_neg]) (by rwa [neg_neg])
    refine ⟨not_isSolved_add_right (hasStride_succ_iff.mp h_hp).1, ?_, ?_, ?_, ?_⟩
    · intro g' hg'
      rw [moves_add] at hg'
      simp only [Set.mem_union, Set.mem_image] at hg'
      obtain ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ := hg'
      · have hx_solved := isSolved_of_mem_moves (hasStride_zero_iff.mp h_gp) hx
        have ⟨mx, _, hmx_s⟩ := hasStride_of_mem_moves_neg h_gn (show x ∈ moves (-(-p)) g by rwa [neg_neg])
        have := hasStride_add (hasStride_zero_iff.mpr hx_solved) h_hp hmx_s h_hn
        rw [Nat.zero_add] at this
        exact ⟨k' + 1, by omega, this⟩
      · have ⟨j, hj, hj_s⟩ := hasStride_of_mem_moves h_hp hx
        have ⟨lx, _, hlx_s⟩ := hasStride_of_mem_moves_neg h_hn (show x ∈ moves (-(-p)) h by rwa [neg_neg])
        have := hasStride_add h_gp hj_s h_gn hlx_s
        rw [Nat.zero_add] at this
        exact ⟨j, by omega, this⟩
    · refine ⟨g + h₁, add_left_mem_moves_add hh1_mem g, ?_, ?_⟩
      · have := hasStride_add h_gp hh1_p h_gn hh1_neg
        rwa [Nat.zero_add] at this
      · intro g'' hg'' m' hm'
        rw [moves_add] at hg''
        simp only [Set.mem_union, Set.mem_image] at hg''
        obtain ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ := hg''
        · have hx_solved := isSolved_of_mem_moves (hasStride_zero_iff.mp h_gp) hx
          have ⟨mx, hmx, hmx_s⟩ := hasStride_of_mem_moves_neg h_gn (show x ∈ moves (-(-p)) g by rwa [neg_neg])
          have h_xp : HasStride (-(-p)) x 0 := by rw [neg_neg]; exact hasStride_zero_iff.mpr hx_solved
          have h_neg_xh : HasStride (-p) (x + h) (mx + l) :=
            hasStride_add hmx_s h_hn h_xp (by rwa [neg_neg])
          rw [hasStride_unique hm' h_neg_xh]
          exact ⟨m + l, by omega, h_neg_gh1⟩
        · have ⟨lx, hlx, hlx_s⟩ := hasStride_of_mem_moves_neg h_hn (show x ∈ moves (-(-p)) h by rwa [neg_neg])
          have ⟨jx, _, hjx_s⟩ := hasStride_of_mem_moves h_hp hx
          have h_neg_gx : HasStride (-p) (g + x) (m + lx) :=
            hasStride_add h_gn hlx_s (by rwa [neg_neg]) (by rwa [neg_neg])
          rw [hasStride_unique hm' h_neg_gx]
          exact ⟨m + l, by omega, h_neg_gh1⟩
    · intro g' hg'
      rw [moves_add] at hg'
      simp only [Set.mem_union, Set.mem_image] at hg'
      obtain ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ := hg'
      · have hx_solved := isSolved_of_mem_moves (hasStride_zero_iff.mp h_gp) hx
        have ⟨mx, _, hmx_s⟩ := hasStride_of_mem_moves h_gn hx
        have := hasStride_add (hasStride_zero_iff.mpr hx_solved) h_hp hmx_s h_hn
        rw [Nat.zero_add] at this
        exact ⟨k' + 1, by omega, this⟩
      · have ⟨j, hj, hj_s⟩ := hasStride_of_mem_moves_neg h_hp hx
        have ⟨lx, _, hlx_s⟩ := hasStride_of_mem_moves h_hn hx
        have := hasStride_add h_gp hj_s h_gn hlx_s
        rw [Nat.zero_add] at this
        exact ⟨j, by omega, this⟩
    · intro h_ne
      rw [moves_add, Set.nonempty_iff_ne_empty.symm] at h_ne
      simp only [Set.Nonempty, Set.mem_union, Set.mem_image] at h_ne
      obtain ⟨_, ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩⟩ := h_ne
      · have hx_solved := isSolved_of_mem_moves (hasStride_zero_iff.mp h_gp) hx
        have ⟨mx, _, hmx_s⟩ := hasStride_of_mem_moves h_gn hx
        have := hasStride_add (hasStride_zero_iff.mpr hx_solved) h_hp hmx_s h_hn
        rw [Nat.zero_add] at this
        exact ⟨x + h, add_right_mem_moves_add hx h, this⟩
      · have h_ne_h : moves (-p) h ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨x, hx⟩
        have ⟨h', hh'_mem, hh'_s⟩ := hasStride_succ_exists_preserve_neg h_hp h_ne_h
        have ⟨lh', _, hlh'_s⟩ := hasStride_of_mem_moves h_hn hh'_mem
        have := hasStride_add h_gp hh'_s h_gn hlh'_s
        rw [Nat.zero_add] at this
        exact ⟨g + h', add_left_mem_moves_add hh'_mem g, this⟩
termination_by (g, h)
decreasing_by form_wf

private theorem hasStride_winsGoingFirst {p : Player} {g : GameForm} {l r : ℕ}
    (h_l : HasStride p g l) (h_r : HasStride (-p) g r) (h_le : l ≤ r) :
    WinsGoingFirst p g := by
  match l with
  | 0 => exact isSolved_winsGoingFirst (hasStride_zero_iff.mp h_l)
  | .succ l' =>
    have ⟨r', hr'⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    subst hr'
    have ⟨g1, hg1_mem, hg1_stride_p, hg1_stride_neg⟩ :=
      hasStride_good_move_neg_stride h_l h_r
    apply winsGoingFirst_of_moves
    use g1, hg1_mem
    rw [not_winsGoingFirst_iff]
    constructor
    · rw [isEndLike_iff_isEnd]
      exact hasStride_succ_not_isEnd hg1_stride_neg
    · intro g2 hg2_mem
      rw [neg_neg]
      match l' with
      | 0 =>
        exact isSolved_winsGoingFirst
          (isSolved_of_isOption (hasStride_zero_iff.mp hg1_stride_p) (IsOption.of_mem_moves hg2_mem))
      | .succ l'' =>
        have ⟨k_p, hk_p_le, hk_p_stride⟩ := hasStride_succ_support_neg hg1_stride_p g2 hg2_mem
        have ⟨k_neg, hk_neg_ge, hk_neg_stride⟩ := hasStride_succ_support hg1_stride_neg g2 hg2_mem
        have h_le' : k_p ≤ k_neg := by omega
        exact hasStride_winsGoingFirst hk_p_stride hk_neg_stride h_le'
termination_by g
decreasing_by form_wf

private theorem hasStride_not_winsGoingFirst {p : Player} {g : GameForm} {l r : ℕ}
    (h_l : HasStride p g l) (h_r : HasStride (-p) g r) (h_gt : r < l) :
    ¬WinsGoingFirst p g := by
  rw [not_winsGoingFirst_iff]
  constructor
  · rw [isEndLike_iff_isEnd]
    have ⟨l', hl'⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    subst hl'
    exact hasStride_succ_not_isEnd h_l
  · intro g' hg'
    obtain ⟨k_p, hk_p_ge, hk_p_stride⟩ := hasStride_of_mem_moves h_l hg'
    have h_neg_stride : ∃ k, k ≤ r ∧ HasStride (-p) g' k := by
      match r with
      | 0 =>
        exact ⟨0, le_refl _, hasStride_zero_iff.mpr (isSolved_of_mem_moves (hasStride_zero_iff.mp h_r) hg')⟩
      | .succ r' =>
        exact hasStride_succ_support_neg h_r g' (by rw [neg_neg]; exact hg')
    obtain ⟨k_neg, hk_neg_le, hk_neg_stride⟩ := h_neg_stride
    have h_le : k_neg ≤ k_p := by omega
    exact hasStride_winsGoingFirst hk_neg_stride (by rwa [neg_neg]) h_le

/--
If game has both strides then they determine who wins going first
-/
theorem hasStride_winsGoingFirst_iff {p : Player} {g : GameForm} {l r : ℕ}
    (h_l : HasStride p g l) (h_r : HasStride (-p) g r) :
    WinsGoingFirst p g ↔ l ≤ r := by
  constructor
  · intro h_wins
    by_contra h
    push_neg at h
    exact hasStride_not_winsGoingFirst h_l h_r h h_wins
  · exact hasStride_winsGoingFirst h_l h_r

/--
If game has both strides then they determine the winner
-/
theorem hasStride_misereOutcome_iff_lt {p : Player} {g : GameForm} {l r : ℕ}
    (h_l : HasStride p g l) (h_r : HasStride (-p) g r) :
    (MisereOutcome g = Outcome.ofPlayer p) ↔ l < r := by
  rw [misereOutcome_eq_player_iff]
  constructor
  · intro ⟨h_l_win, h_r_win⟩
    rw [hasStride_winsGoingFirst_iff h_l h_r] at h_l_win
    rw [<-neg_neg p] at h_l
    rw [(hasStride_winsGoingFirst_iff h_r h_l).not] at h_r_win
    exact Nat.lt_of_not_le h_r_win
  · intro h_lt
    apply And.intro ((hasStride_winsGoingFirst_iff h_l h_r).mpr (Nat.le_of_succ_le h_lt))
    rw [<-neg_neg p] at h_l
    rw [(hasStride_winsGoingFirst_iff h_r h_l).not]
    exact Nat.not_le_of_lt h_lt

/--
If game has both strides then they determine the winner
-/
theorem hasStride_misereOutcome_iff_eq {p : Player} {g : GameForm} {l r : ℕ}
    (h_l : HasStride p g l) (h_r : HasStride (-p) g r) :
    (MisereOutcome g = .N) ↔ l = r := by
  rw [misereOutcome_N_iff_winsGoingFirst]
  cases p
  · rw [hasStride_winsGoingFirst_iff h_l h_r]
    rw [<-neg_neg Player.left] at h_l
    rw [<-Player.neg_left, hasStride_winsGoingFirst_iff h_r h_l]
    exact Nat.le_antisymm_iff.symm
  · rw [hasStride_winsGoingFirst_iff h_l h_r]
    rw [<-neg_neg Player.right] at h_l
    rw [<-Player.neg_right, hasStride_winsGoingFirst_iff h_r h_l]
    exact Iff.symm ge_antisymm_iff

/--
If game has both strides then it is P-free
-/
theorem hasStride_isPFree {p : Player} {g : GameForm} {l r : ℕ}
    (h_l : HasStride p g l) (h_r : HasStride (-p) g r) : IsPFree g := by
  unfold IsPFree
  constructor
  · obtain h_lt | h_eq | h_gt := Nat.lt_trichotomy l r
    · rw [(hasStride_misereOutcome_iff_lt h_l h_r).mpr h_lt]
      cases p <;> simp
    · rw [(hasStride_misereOutcome_iff_eq h_l h_r).mpr h_eq]
      simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    · rw [<-neg_neg p] at h_l
      rw [(hasStride_misereOutcome_iff_lt h_r h_l).mpr h_gt]
      cases p <;> simp
  · intro q g' h_g'_mem
    by_cases h_pq : p = q
    · subst h_pq
      have ⟨_, _, h_l'⟩ := hasStride_of_mem_moves h_l h_g'_mem
      rw [<-neg_neg p] at h_g'_mem
      have ⟨_, _, h_r'⟩ := hasStride_of_mem_moves_neg h_r h_g'_mem
      exact hasStride_isPFree h_l' h_r'
    · simp only [Player.ne_iff_eq_neg] at h_pq; subst h_pq
      rw [<-neg_neg q] at h_g'_mem
      have ⟨_, _, h_r'⟩ := hasStride_of_mem_moves (g' := g') h_r h_g'_mem
      have ⟨_, _, h_l'⟩ := hasStride_of_mem_moves_neg (g' := g') h_l h_g'_mem
      exact hasStride_isPFree h_l' h_r'
termination_by g
decreasing_by form_wf

end GameForm
