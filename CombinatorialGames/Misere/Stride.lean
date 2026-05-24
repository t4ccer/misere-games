/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.GameForm
public import CombinatorialGames.Form.Misere.Outcome
public import CombinatorialGames.Misere.PFree
public import CombinatorialGames.Misere.Quotient
public import CombinatorialGames.AdditiveClosure
public import CombinatorialGames.Ruleset

universe u

public section

namespace GameForm

open Form
open Form.Misere.Outcome
open Ruleset

/--
Intuitively a position is solved for a given player if they win no matter what they do
-/
def IsSolved (p : Player) (g : GameForm) : Prop :=
  (IsOption 0 g → 0 ∉ moves p g)
  ∧ (g ≠ 0 → ¬IsEnd (-p) g)
  ∧ (∀ gp, IsOption gp g → IsSolved p gp)
termination_by g
decreasing_by form_wf

theorem isSolved_def (p : Player) (g : GameForm) :
  IsSolved p g ↔
    ((IsOption 0 g → 0 ∉ moves p g)
    ∧ (g ≠ 0 → ¬IsEnd (-p) g)
    ∧ (∀ gp, IsOption gp g → IsSolved p gp)) := by
  constructor
  · intro h; unfold IsSolved at h; exact h
  · intro h; unfold IsSolved; exact h

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
  rw [add_comm]
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

theorem hasStride_misereOutcome_iff_ge {p : Player} {g : GameForm} {l r : ℕ}
    (h_l : HasStride p g l) (h_r : HasStride (-p) g r) :
    (MisereOutcome g = Outcome.ofPlayer (-p)) ↔ l > r := by
  refine hasStride_misereOutcome_iff_lt h_r ?_
  rwa [neg_neg]

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

class Strided (A : GameForm → Prop) where
  mk_with_strides (l r : ℕ) : ∃ g, A g ∧ HasStride .left g l ∧ HasStride .right g r
  has_stride (p : Player) {g : GameForm} (h_g : A g) : ∃ n, GameForm.HasStride p g n

theorem AdditiveClosure.has_stride_aux {R : Type u} [Ruleset R] (p : Player) {g : GameForm}
    (stride : R → Player → ℕ)
    (hasStride : (r : R) → (p : Player) → GameForm.HasStride p (Ruleset.toGameForm r) (stride r p))
    (h_g : AdditiveClosure (Ruleset.Forms R) g)
    : ∃ n, GameForm.HasStride p g n := by
  rw [additiveClosure_iff] at h_g
  obtain h_g | ⟨x, y, hx, hy, hxy, hax, hay⟩ := h_g
  · obtain ⟨r, h_r⟩ := Ruleset.Forms.exists h_g
    have := hasStride r p
    use stride r p
    rwa [h_r]
  · have ⟨a, ha⟩ := has_stride_aux p stride hasStride hax
    have ⟨a', ha'⟩ := has_stride_aux (-p) stride hasStride hax
    have ⟨b, hb⟩ := has_stride_aux p stride hasStride hay
    have ⟨b', hb'⟩ := has_stride_aux (-p) stride hasStride hay
    use a + b
    rw [hxy]
    exact GameForm.hasStride_add ha hb ha' hb'
termination_by Form.birthday g
decreasing_by
  all_goals
  · subst hxy
    simp only [Form.birthday_add, lt_add_iff_pos_left, lt_add_iff_pos_right]
    by_contra h_absurd
    simp only [not_lt, NatOrdinal.le_zero, GameForm.birthday_eq_zero] at h_absurd
    absurd h_absurd
    assumption

theorem AdditiveClosure.mk_with_strides_aux {A : GameForm → Prop}
    (mk_stride_other_zero : (p : Player) → (n : ℕ) → ∃ g, A g ∧ HasStride p g n ∧ HasStride (-p) g 0)
    (l r : ℕ) :
    ∃ t, AdditiveClosure A t ∧ HasStride .left t l ∧ HasStride .right t r := by
  obtain ⟨t₁, ht₁_A, ht₁_l, ht₁_r⟩ := mk_stride_other_zero .left l
  have ht₁_A' := additiveClosure_iff.mpr (Or.inl ht₁_A)
  obtain ⟨t₂, ht₂_A, ht₂_r, ht₂_l⟩ := mk_stride_other_zero .right r
  have ht₂_A' := additiveClosure_iff.mpr (Or.inl ht₂_A)
  use t₁ + t₂
  refine ⟨ClosedUnderAdd.has_add _ _ ht₁_A' ht₂_A', ?_, ?_⟩
  · have := hasStride_add ht₁_l ht₂_l ht₁_r ht₂_r
    simpa only [add_zero] using this
  · have := hasStride_add ht₁_r ht₂_r ht₁_l ht₂_l
    simpa only [zero_add] using this

section Quotients

variable {A : GameForm → Prop} [Strided A]

theorem stride_diff_eq_of_misereEQ
    {g h : GameForm}
    (_h_g : A g) (_h_h : A h) (h_eq : g =m A h)
    {ng rg nh rh : ℕ}
    (h_ng : HasStride .left g ng) (h_rg : HasStride .right g rg)
    (h_nh : HasStride .left h nh) (h_rh : HasStride .right h rh) :
    (ng : ℤ) - (rg : ℤ) = (nh : ℤ) - (rh : ℤ) := by
  -- Construct a test game t with left stride rg and right stride ng.
  -- Then g + t has equal left and right strides (both ng + rg), giving outcome N.
  -- Since g =m A h, h + t also has outcome N, forcing nh + rg = rh + ng.
  obtain ⟨t, ht_A, ht_l, ht_r⟩ := Strided.mk_with_strides (A := A) rg ng
  have h_outcome_g : MisereOutcome (g + t) = .N := by
    rw [(hasStride_misereOutcome_iff_eq
      (hasStride_add h_ng ht_l h_rg ht_r)
      (hasStride_add h_rg ht_r h_ng ht_l))]
    omega
  have h_eq_t := (h_eq t ht_A).symm
  rw [h_outcome_g] at h_eq_t
  rw [(hasStride_misereOutcome_iff_eq
    (hasStride_add h_nh ht_l h_rh ht_r)
    (hasStride_add h_rh ht_r h_nh ht_l))] at h_eq_t
  omega

/-
Two games with the same stride difference are misère equivalent.
-/
theorem misereEQ_of_stride_diff_eq
    {g h : GameForm}
    {ng rg nh rh : ℕ}
    (h_ng : HasStride .left g ng) (h_rg : HasStride .right g rg)
    (h_nh : HasStride .left h nh) (h_rh : HasStride .right h rh)
    (h_diff : (ng : ℤ) - (rg : ℤ) = (nh : ℤ) - (rh : ℤ)) :
    g =m A h := by
  intro t ht
  obtain ⟨lt, h_lt⟩ := (Strided.has_stride .left ht)
  obtain ⟨rt, h_rt⟩ := (Strided.has_stride .right ht);
  have h_add1 := hasStride_add h_ng h_lt h_rg h_rt
  have h_add2 := hasStride_add h_rg h_rt h_ng h_lt
  have h_add3 := hasStride_add h_nh h_lt h_rh h_rt
  have h_add4 := hasStride_add h_rh h_rt h_nh h_lt

  have h_outcome1 := hasStride_misereOutcome_iff_eq h_add1 h_add2
  have h_outcome2 := hasStride_misereOutcome_iff_eq h_add3 h_add4
  have h_outcome3 := hasStride_misereOutcome_iff_lt h_add1 h_add2
  have h_outcome4 := hasStride_misereOutcome_iff_lt h_add3 h_add4
  have h_outcome5 : MisereOutcome (g + t) = .R ↔ ng + lt > rg + rt :=
    hasStride_misereOutcome_iff_ge h_add1 h_add2
  have h_outcome6 : MisereOutcome (h + t) = .R ↔ nh + lt > rh + rt :=
    hasStride_misereOutcome_iff_ge h_add3 h_add4

  grind only

/--
The stride difference characterizes misère equivalence for strided games.
-/
theorem misereEQ_iff_stride_diff_eq
    {g h : GameForm}
    (h_g : A g) (h_h : A h)
    {ng rg nh rh : ℕ}
    (h_ng : HasStride .left g ng) (h_rg : HasStride .right g rg)
    (h_nh : HasStride .left h nh) (h_rh : HasStride .right h rh) :
    (g =m A h) ↔ ((ng : ℤ) - (rg : ℤ) = (nh : ℤ) - (rh : ℤ)) :=
  ⟨fun heq => stride_diff_eq_of_misereEQ (A := A) h_g h_h heq h_ng h_rg h_nh h_rh,
   fun hdiff => misereEQ_of_stride_diff_eq h_ng h_rg h_nh h_rh hdiff⟩

/-
If the stride difference of g is ≤ that of h (as integers), then g ≥m A h.
Lower stride diff means better for Left, so higher MisereOutcome.
-/
theorem misereGE_of_stride_diff_le
    {g h : GameForm}
    (_h_g : A g) (_h_h : A h)
    {ng rg nh rh : ℕ}
    (h_ng : HasStride .left g ng) (h_rg : HasStride .right g rg)
    (h_nh : HasStride .left h nh) (h_rh : HasStride .right h rh)
    (h_le : (ng : ℤ) - (rg : ℤ) ≤ (nh : ℤ) - (rh : ℤ)) :
    g ≥m A h := by
  intro x hx;
  -- By hasStride_add: g+x has strides (ng+lx, rg+rx), h+x has strides (nh+lx, rh+rx).
  obtain ⟨lx, hx_l⟩ : ∃ lx, HasStride Player.left x lx :=
    ‹Strided A›.has_stride .left hx
  obtain ⟨rx, hx_r⟩ : ∃ rx, HasStride Player.right x rx :=
    ‹Strided A›.has_stride .right hx
  have h_gx : HasStride Player.left (g + x) (ng + lx) := by
    apply hasStride_add h_ng hx_l h_rg hx_r
  have h_rx : HasStride Player.right (g + x) (rg + rx) := by
    apply hasStride_add
    all_goals tauto
  have h_hx : HasStride Player.left (h + x) (nh + lx) := hasStride_add h_nh hx_l h_rh hx_r
  have h_rx' : HasStride Player.right (h + x) (rh + rx) := hasStride_add h_rh hx_r h_nh hx_l
  have h_outcome_gx :
      MisereOutcome (g + x) =
      if ng + lx < rg + rx then .L else if ng + lx = rg + rx then .N else .R := by
    have h1 := hasStride_misereOutcome_iff_lt h_gx h_rx
    have h2 := hasStride_misereOutcome_iff_eq h_gx h_rx
    have h3 := hasStride_misereOutcome_iff_lt h_rx h_gx
    have h4 := hasStride_misereOutcome_iff_eq h_rx h_gx
    simp only [Outcome.ofPlayer_left, Outcome.ofPlayer_right] at h1 h2 h3 h4
    grind only
  have h_outcome_hx : MisereOutcome (h + x) = if nh + lx < rh + rx then .L else if nh + lx = rh + rx then .N else .R := by
    have h_outcome_hx : MisereOutcome (h + x) = .L ↔ nh + lx < rh + rx := by
      convert hasStride_misereOutcome_iff_lt h_hx h_rx' using 1
    have h_outcome_hx' : MisereOutcome (h + x) = .N ↔ nh + lx = rh + rx :=
      hasStride_misereOutcome_iff_eq h_hx h_rx'
    have h_outcome_hx'' : MisereOutcome (h + x) = .R ↔ nh + lx > rh + rx := by
      convert hasStride_misereOutcome_iff_lt ( p := .right ) h_rx' h_hx using 1
    grind only
  split_ifs at *
    <;> simp_all +decide only [tsub_le_iff_right, lt_self_iff_false, not_false_eq_true, ge_iff_le]
  · grind only
  · omega
  · omega

/--
The misère quotient of a strided class is totally ordered.
This follows from the fact that the ordering is determined by stride differences.
-/
theorem misereQuotient_linearOrder (a b : MisereQuotient A) : a ≤ b ∨ b ≤ a := by
  have ha : A ↑(Form.MisereQuotient.out a) := (Form.MisereQuotient.out a).prop
  have hb : A ↑(Form.MisereQuotient.out b) := (Form.MisereQuotient.out b).prop
  obtain ⟨la, hla⟩ := Strided.has_stride (A := A) .left ha
  obtain ⟨ra, hra⟩ := Strided.has_stride (A := A) .right ha
  obtain ⟨lb, hlb⟩ := Strided.has_stride (A := A) .left hb
  obtain ⟨rb, hrb⟩ := Strided.has_stride (A := A) .right hb
  rcases le_total ((lb : ℤ) - rb) ((la : ℤ) - ra) with h | h
  · exact Or.inl (misereGE_of_stride_diff_le hb ha hlb hrb hla hra h)
  · exact Or.inr (misereGE_of_stride_diff_le ha hb hla hra hlb hrb h)

/--
The stride difference of a game in a strided class `A`.
This is the left stride minus the right stride, as an integer.
-/
noncomputable def Strided.strideDiff
    (g : GameForm) (hg : A g) : ℤ :=
  ((Strided.has_stride (A := A) .left hg).choose : ℤ) -
  ((Strided.has_stride (A := A) .right hg).choose : ℤ)

/--
The stride difference is well-defined regardless of which stride witnesses are used.
-/
theorem strideDiff_eq
    {g : GameForm} {hg : A g}
    {l r : ℕ} (hl : HasStride .left g l) (hr : HasStride .right g r) :
    Strided.strideDiff g hg = (l : ℤ) - (r : ℤ) := by
  unfold Strided.strideDiff
  have h1 := hasStride_unique (Strided.has_stride (A := A) .left hg).choose_spec hl
  have h2 := hasStride_unique (Strided.has_stride (A := A) .right hg).choose_spec hr
  rw [h1, h2]

/--
Misère equivalent games have the same stride difference.
-/
theorem Strided.strideDiff_eq_of_misereEQ
    {g h : GameForm} (hg : A g) (hh : A h) (heq : g =m A h) :
    Strided.strideDiff g hg = Strided.strideDiff h hh := by
  obtain ⟨lg, hlg⟩ := Strided.has_stride (A := A) .left hg
  obtain ⟨rg, hrg⟩ := Strided.has_stride (A := A) .right hg
  obtain ⟨lh, hlh⟩ := Strided.has_stride (A := A) .left hh
  obtain ⟨rh, hrh⟩ := Strided.has_stride (A := A) .right hh
  rw [strideDiff_eq hlg hrg, strideDiff_eq hlh hrh]
  exact stride_diff_eq_of_misereEQ hg hh heq hlg hrg hlh hrh

/--
The stride difference function on the misère quotient, defined via representative.
This is well-defined because misère equivalent games have the same stride difference.
-/
noncomputable def MisereQuotient.strideDiff : MisereQuotient A → ℤ := by
  apply Quotient.lift (fun (g : {g : GameForm // A g}) => Strided.strideDiff g g.prop)
  intro g h heq
  unfold MisereSetoid at heq
  exact Strided.strideDiff_eq_of_misereEQ g.prop h.prop heq

theorem MisereQuotient.strideDiff_mk (g : GameForm) (hg : A g) :
    strideDiff (MisereQuotient.mk A g hg) = Strided.strideDiff g hg := by
  simp only [strideDiff, MisereQuotient.mk, Quotient.lift_mk]

/--
The stride difference function on the quotient is injective.
-/
theorem MisereQuotient.strideDiff_injective : Function.Injective (strideDiff (A := A)) := by
  intro a b hab
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
    apply Quotient.sound'
    show (a : GameForm) =m A (b : GameForm)
    obtain ⟨la, hla⟩ := Strided.has_stride (A := A) .left a.prop
    obtain ⟨ra, hra⟩ := Strided.has_stride (A := A) .right a.prop
    obtain ⟨lb, hlb⟩ := Strided.has_stride (A := A) .left b.prop
    obtain ⟨rb, hrb⟩ := Strided.has_stride (A := A) .right b.prop
    have ha : Strided.strideDiff a a.prop = (la : ℤ) - (ra : ℤ) := strideDiff_eq hla hra
    have hb : Strided.strideDiff b b.prop = (lb : ℤ) - (rb : ℤ) := strideDiff_eq hlb hrb
    change Strided.strideDiff a a.prop = Strided.strideDiff b b.prop at hab
    rw [ha, hb] at hab
    exact misereEQ_of_stride_diff_eq hla hra hlb hrb hab

/--
The stride difference function on the quotient is surjective:
for any integer `d`, there is a game in `A` with stride difference `d`.
-/
theorem MisereQuotient.strideDiff_surjective : Function.Surjective (strideDiff (A := A)) := by
  intro d
  obtain ⟨n, m, rfl⟩ : ∃ n m : ℕ, d = (n : ℤ) - (m : ℤ) := by
    match d with
    | .ofNat n =>
      use n, 0
      simp only [Int.ofNat_eq_natCast, Nat.cast_zero, sub_zero]
    | .negSucc n =>
      use 0, n + 1
      simp only [Int.negSucc_eq, neg_add_rev, Int.reduceNeg, Nat.cast_zero, Nat.cast_add,
                 Nat.cast_one, zero_sub]
  obtain ⟨t, ht_A, ht_l, ht_r⟩ := Strided.mk_with_strides (A := A) n m
  use Form.MisereQuotient.mk A t ht_A
  rw [MisereQuotient.strideDiff_mk]
  exact strideDiff_eq ht_l ht_r

/--
The misère quotient of a strided class is equivalent to the integers.
The equivalence sends each equivalence class to its stride difference.
-/
noncomputable def MisereQuotient.stridedEquivInt : MisereQuotient A ≃ ℤ :=
  Equiv.ofBijective MisereQuotient.strideDiff
    ⟨MisereQuotient.strideDiff_injective, MisereQuotient.strideDiff_surjective⟩

/--
If `g ≥m A h` then the stride difference of `g` is `≤` that of `h`.
The converse of `misereGE_of_stride_diff_le`.
-/
theorem stride_diff_le_of_misereGE
    {g h : GameForm}
    (h_g : A g) (h_h : A h) (h_ge : g ≥m A h)
    {ng rg nh rh : ℕ}
    (h_ng : HasStride .left g ng) (h_rg : HasStride .right g rg)
    (h_nh : HasStride .left h nh) (h_rh : HasStride .right h rh) :
    (ng : ℤ) - (rg : ℤ) ≤ (nh : ℤ) - (rh : ℤ) := by
  by_contra h_lt
  push_neg at h_lt
  have h_ge' : h ≥m A g :=
    misereGE_of_stride_diff_le h_h h_g h_nh h_rh h_ng h_rg (Int.le_of_lt h_lt)
  have h_eq : g =m A h := MisereEq.of_antisymm h_ge h_ge'
  have h_eq_diff := stride_diff_eq_of_misereEQ h_g h_h h_eq h_ng h_rg h_nh h_rh
  omega

/--
Misère GE is equivalent to stride difference inequality.
-/
theorem misereGE_iff_stride_diff_le
    {g h : GameForm} (h_g : A g) (h_h : A h)
    {ng rg nh rh : ℕ}
    (h_ng : HasStride .left g ng) (h_rg : HasStride .right g rg)
    (h_nh : HasStride .left h nh) (h_rh : HasStride .right h rh) :
    (g ≥m A h) ↔ ((ng : ℤ) - (rg : ℤ) ≤ (nh : ℤ) - (rh : ℤ)) :=
  ⟨fun hge => stride_diff_le_of_misereGE h_g h_h hge h_ng h_rg h_nh h_rh,
   fun hle => misereGE_of_stride_diff_le h_g h_h h_ng h_rg h_nh h_rh hle⟩

/--
The ordering on the misère quotient corresponds to `≥` on stride differences:
`mk A g hg ≤ mk A h hh` iff `strideDiff A g hg ≥ strideDiff A h hh`.
-/
theorem MisereQuotient.mk_le_iff_strideDiff
    (g h : GameForm) (hg : A g) (hh : A h) :
    MisereQuotient.mk A g hg ≤ MisereQuotient.mk A h hh ↔
      Strided.strideDiff g hg ≥ Strided.strideDiff h hh := by
  obtain ⟨lg, hlg⟩ := Strided.has_stride (A := A) .left hg
  obtain ⟨rg, hrg⟩ := Strided.has_stride (A := A) .right hg
  obtain ⟨lh, hlh⟩ := Strided.has_stride (A := A) .left hh
  obtain ⟨rh, hrh⟩ := Strided.has_stride (A := A) .right hh
  rw [strideDiff_eq hlg hrg, strideDiff_eq hlh hrh]
  constructor
  · intro hab
    have hge : h ≥m A g :=
      misereGE_rw_left (Form.MisereQuotient.mk_out_equiv h)
        (misereGE_rw_right (MisereEQ.symm (Form.MisereQuotient.mk_out_equiv g)) hab)
    exact stride_diff_le_of_misereGE hh hg hge hlh hrh hlg hrg
  · intro hge
    have h_ge : h ≥m A g :=
      misereGE_of_stride_diff_le hh hg hlh hrh hlg hrg hge
    exact misereGE_rw_left (MisereEQ.symm (Form.MisereQuotient.mk_out_equiv h))
      (misereGE_rw_right (Form.MisereQuotient.mk_out_equiv g) h_ge)

theorem MisereQuotient.le_iff_strideDiff_ge (a b : MisereQuotient A) :
    a ≤ b ↔ MisereQuotient.strideDiff a ≥ MisereQuotient.strideDiff b := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
    simp only [MisereQuotient.strideDiff, Quotient.lift_mk]
    show Form.MisereQuotient.mk A a a.prop ≤ Form.MisereQuotient.mk A b b.prop ↔
      Strided.strideDiff a a.prop ≥ Strided.strideDiff b b.prop
    exact mk_le_iff_strideDiff a b a.prop b.prop

/--
The misère quotient ordering via the integer equivalence: `a ≤ b` iff
the image of `a` under the equivalence is ≥ the image of `b`.
Equivalently, the equivalence is an order-reversing bijection.
-/
theorem MisereQuotient.le_iff_equiv_ge (a b : MisereQuotient A) :
    a ≤ b ↔ MisereQuotient.stridedEquivInt a ≥ MisereQuotient.stridedEquivInt b := by
  exact MisereQuotient.le_iff_strideDiff_ge a b

end Quotients

end GameForm
