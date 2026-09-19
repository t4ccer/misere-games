/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.GameForm
public import CombinatorialGames.GameForm.OrdinalSum
public import CombinatorialGames.Form.Misere.Outcome
public import CombinatorialGames.Misere.PFree
public import CombinatorialGames.Misere.DeadEnding
public import CombinatorialGames.Misere.Quotients
public import CombinatorialGames.Misere.Closures
public import CombinatorialGames.Ruleset

universe u

public section

namespace GameForm

open Form
open Form.Misere.Outcome
open Ruleset

/-! ## Solved -/

/--
Intuitively, a position is *solved* for a given player if they win regardless
of the moves they make.
-/
def IsSolved (p : Player) (g : GameForm) : Prop :=
  (0 ∉ moves p g)
  ∧ (g ≠ 0 → ¬IsEnd (-p) g)
  ∧ (∀ gp, IsOption gp g → IsSolved p gp)
termination_by g
decreasing_by form_wf

theorem isSolved_def (p : Player) (g : GameForm) :
  IsSolved p g ↔
    ((0 ∉ moves p g)
    ∧ (g ≠ 0 → ¬IsEnd (-p) g)
    ∧ (∀ gp, IsOption gp g → IsSolved p gp)) := by
  constructor
  · intro h; unfold IsSolved at h; exact h
  · intro h; unfold IsSolved; exact h

theorem isSolved_zero_not_mem {p : Player} {g : GameForm} (h_isSolved : IsSolved p g) :
    0 ∉ moves p g := by
  unfold IsSolved at h_isSolved
  exact h_isSolved.left

theorem isSolved_zero_mem {p : Player} {g : GameForm}
    (h_isSolved : IsSolved p g) (h_isOption : IsOption 0 g) :
    0 ∈ moves (-p) g := by
  unfold IsSolved at h_isSolved
  have h_not_mem := h_isSolved.left
  exact isOption_not_mem h_isOption h_not_mem

theorem isSolved_not_isEnd {p : Player} {g : GameForm}
    (h_isSolved : IsSolved p g) (h_ne_zero : g ≠ 0) : ¬IsEnd (-p) g := by
  unfold IsSolved at h_isSolved
  exact h_isSolved.right.left h_ne_zero

theorem isSolved_of_isOption {g gp : GameForm} {p : Player} (h1 : IsSolved p g) (h2 : IsOption gp g) :
    IsSolved p gp := by
  unfold IsSolved at h1
  exact h1.right.right gp h2

theorem isSolved_of_subposition {g gp : GameForm} {p : Player} (h1 : IsSolved p g) (h2 : Subposition gp g) :
    IsSolved p gp := by
  unfold Subposition at h2
  match h2 with
  | .single h_isOption => exact isSolved_of_isOption h1 h_isOption
  | .tail h3 h_isOption =>
    rw [<-Subposition] at h3
    exact isSolved_of_subposition (isSolved_of_isOption h1 h_isOption) h3
termination_by g
decreasing_by form_wf

theorem isSolved_of_mem_moves {p : Player} {g g' : GameForm} {q : Player}
    (h : IsSolved p g) (hm : g' ∈ moves q g) : IsSolved p g' :=
  isSolved_of_isOption h (IsOption.of_mem_moves hm)

private theorem isSolved_neg {p : Player} {g : GameForm} (h_isSolved : IsSolved p g) :
    IsSolved (-p) (-g) := by
  unfold IsSolved
  refine ⟨?_, ?_, ?_⟩
  · intro h_zero_mem
    simp only [moves_neg, neg_neg, Set.mem_neg, neg_zero] at h_zero_mem
    exact isSolved_zero_not_mem h_isSolved h_zero_mem
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
decreasing_by  -- FIXME: Derive birthday bounds from IsOption
  rw [isOption_neg] at h_isOption
  exact birthday_lt_of_isOption h_isOption

@[simp]
theorem isSolved_neg_iff {p : Player} {g : GameForm} : IsSolved (-p) (-g) ↔ IsSolved p g := by
  constructor
  · intro h_isSolved
    have h_isSolved_neg := isSolved_neg h_isSolved
    rwa [neg_neg, neg_neg] at h_isSolved_neg
  · exact isSolved_neg

@[simp]
theorem isSolved_neg_iff' {p : Player} {g : GameForm} : IsSolved p (-g) ↔ IsSolved (-p) g := by
  rw [<-neg_neg p, isSolved_neg_iff, neg_neg]

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
      exact isSolved_zero_not_mem h_isSolved h_gp_mem
    apply winsGoingFirst_of_moves
    use gp, h_gp_mem
    rw [not_winsGoingFirst_iff]
    -- Now since G^P ≠ 0 it cannot be a -p end since G is solved for P and
    -- every subposition of G^P is winning if p goes first by induction.
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
The sum of two solved games is solved.
-/
theorem isSolved_add {p : Player} {g h : GameForm}
    (h_isSolved_g : IsSolved p g) (h_isSolved_h : IsSolved p h) : IsSolved p (g + h) := by
  unfold IsSolved
  refine ⟨?_, ?_, ?_⟩
  · intro h_zero_gh
    simp only [moves_add, Set.mem_union, Set.mem_image, add_eq_zero_iff, ↓existsAndEq, true_and, exists_eq_right_right] at h_zero_gh
    apply Or.elim h_zero_gh
    · intro ⟨h_zero_g, _⟩
      exact isSolved_zero_not_mem h_isSolved_g h_zero_g
    · intro ⟨h_zero_h, _⟩
      exact isSolved_zero_not_mem h_isSolved_h h_zero_h
  · intro h_gh_ne_zero
    have h_not_gh_zero := (add_eq_zero_iff (G := GameForm) (x := g) (y := h)).not.mp h_gh_ne_zero
    rw [not_and_or] at h_not_gh_zero
    apply Or.elim h_not_gh_zero
    · intro h_g_ne_zero
      exact not_isEnd_add_left (isSolved_not_isEnd h_isSolved_g h_g_ne_zero)
    · intro h_h_ne_zero
      exact not_isEnd_add_right (isSolved_not_isEnd h_isSolved_h h_h_ne_zero)
  · intro ghp h_isOption_ghp
    simp only [isOption_iff_mem_moves, moves_add, Set.mem_union, Set.mem_image] at h_isOption_ghp
    obtain ⟨p, ⟨x, h_x_mem, h_xh⟩ | ⟨x, h_x_mem, h_gx⟩⟩ := h_isOption_ghp
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

/-! ### Ordinal sums -/

/--
Solvedness of an ordinal sum only sees the base: the branch can only be
reached through the base, and every subposition of the base is a subposition
of the ordinal sum.
-/
theorem isSolved_of_isSolved_ordinalSum {p : Player} {x y : GameForm}
    (h : IsSolved p (ordinalSum x y)) : IsSolved p x := by
  by_cases h_end : IsEnd (-p) y
  · rw [isSolved_def]
    refine ⟨?_, ?_, ?_⟩
    · intro h_zero
      exact isSolved_zero_not_mem h (mem_moves_ordinalSum_base y h_zero)
    · intro h_ne_zero h_x_end
      exact isSolved_not_isEnd h (ordinalSum_ne_zero y h_ne_zero)
        (isEnd_ordinalSum_iff.mpr ⟨h_x_end, h_end⟩)
    · intro x' h_x'
      exact isSolved_of_isOption h (IsOption.ordinalSum_base y h_x')
  · obtain ⟨y', h_y'⟩ := not_isEnd_exists_move h_end
    exact isSolved_of_isSolved_ordinalSum
      (isSolved_of_mem_moves h (mem_moves_ordinalSum_branch x h_y'))
termination_by y
decreasing_by form_wf

theorem isSolved_ordinalSum {p : Player} {x : GameForm} (y : GameForm) (h_ne_zero : x ≠ 0)
    (h : IsSolved p x) : IsSolved p (ordinalSum x y) := by
  rw [isSolved_def]
  refine ⟨?_, ?_, ?_⟩
  · intro h_zero
    rw [mem_moves_ordinalSum_iff] at h_zero
    obtain h_zero | ⟨y', _, h_zero⟩ := h_zero
    · exact isSolved_zero_not_mem h h_zero
    · exact ordinalSum_ne_zero y' h_ne_zero h_zero.symm
  · intro _ h_end
    exact isSolved_not_isEnd h h_ne_zero (isEnd_ordinalSum_iff.mp h_end).1
  · intro z h_z
    rw [isOption_ordinalSum_iff] at h_z
    obtain h_z | ⟨y', h_y', rfl⟩ := h_z
    · exact isSolved_of_isOption h h_z
    · exact isSolved_ordinalSum y' h_ne_zero h
termination_by y
decreasing_by form_wf

theorem isSolved_ordinalSum_iff {p : Player} {x y : GameForm} (h_ne_zero : x ≠ 0) :
    IsSolved p (ordinalSum x y) ↔ IsSolved p x :=
  ⟨isSolved_of_isSolved_ordinalSum, isSolved_ordinalSum y h_ne_zero⟩

/-! ### Integers -/

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
    -- Then since G is solved for Left, G is not a Right end so there exists
    -- some G^R
    have ⟨gr, h_gr_mem_r⟩ := not_isEnd_exists_move (isSolved_not_isEnd h_isSolved_left h_ne_zero)
    -- Since G is solved for both players, G^R is also solved by both players
    -- so by induction G^R = 0
    have h_gr := isSolved_iff_zero.mp
                 ⟨ isSolved_of_isOption h_isSolved_left (IsOption.of_mem_moves h_gr_mem_r)
                 , isSolved_of_isOption h_isSolved_right (IsOption.of_mem_moves h_gr_mem_r)⟩
    subst h_gr
    -- But G is solved for Right so 0 cannot be a Left option of G
    exact isSolved_zero_not_mem h_isSolved_right h_gr_mem_r
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

@[simp]
theorem not_isSolved_left_one : ¬IsSolved .left 1 := by
  intro h1
  simpa using isSolved_iff_zero.mp ⟨h1, isSolved_right_one⟩

theorem isSolved_deadEnd {p : Player} {g : GameForm} (h_deadEnd : IsDeadEnd p g) : IsSolved p g := by
  rw [isSolved_def]
  refine ⟨?_, ?_, ?_⟩
  · exact not_mem_moves_of_isEnd (isEnd_of_isDeadEnd h_deadEnd)
  · intro h_ne_zero
    exact zero_not_both_end h_ne_zero (isEnd_of_isDeadEnd h_deadEnd)
  · intro gp h_isOption
    exact isSolved_deadEnd (isDeadEnd_of_isOption h_deadEnd h_isOption)
termination_by g
decreasing_by form_wf

/-! ## Strides -/

/--
Stride measures exactly how many moves away each player is from a solved
position: the `p`-stride of `g` is `0` iff `g` is solved for `p`, every
`p`-move lowers it by at most one, some `p`-move lowers it by exactly one
without changing the opponent's stride, and no opponent move raises it.

The last requirement on the best move refers to the opponent's stride of `g`
itself, which would make the definition loopy. Instead we compare against the
opponent's *candidate* stride, the value the opponent's stride would have to
take judged from the opponent's options alone (see `StrideCandidate`); when
the opponent's stride exists the two agree (`hasStride_strideCandidate`).

Stride is not well-defined for all game forms: `*` has none, and neither does
`{0 | -1}`.
-/
def HasStride (p : Player) (g : GameForm) (n : ℕ) : Prop :=
  match n with
  | 0 => IsSolved p g
  | n + 1 =>
    ¬IsSolved p g
    ∧ (∀ g' ∈ moves p g, ∃ k, n ≤ k ∧ HasStride p g' k)
    ∧ (∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n
        ∧ ∃ m, HasStride (-p) g' m
          ∧ match m with
            | 0 => IsSolved (-p) g
            | m + 1 =>
              ¬IsSolved (-p) g
              ∧ (∀ g'' ∈ moves (-p) g, ∃ k, m ≤ k ∧ HasStride (-p) g'' k)
              ∧ (∃ g'', ∃ (_ : g'' ∈ moves (-p) g), HasStride (-p) g'' m))
    ∧ (∀ g' ∈ moves (-p) g, ∃ k, k ≤ n + 1 ∧ HasStride p g' k)
termination_by g
decreasing_by form_wf

/--
The value that the `p`-stride of `g` must take if it exists, determined by the
strides of the `p`-options alone: `0` when `g` is solved, otherwise one more
than the smallest stride of a `p`-option.
-/
def StrideCandidate (p : Player) (g : GameForm) (m : ℕ) : Prop :=
  match m with
  | 0 => IsSolved p g
  | m + 1 =>
    ¬IsSolved p g
    ∧ (∀ g' ∈ moves p g, ∃ k, m ≤ k ∧ HasStride p g' k)
    ∧ (∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' m)

/--
The stride equals zero if the game is solved.
-/
@[simp]
theorem hasStride_eq_zero_iff {p : Player} {g : GameForm} :
    HasStride p g 0 ↔ IsSolved p g := by
  constructor
  · intro h; unfold HasStride at h; exact h
  · intro h; unfold HasStride; exact h

/--
A game is solved if its stride equals zero.
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

theorem hasStride_not_isSolved_iff_pos {p : Player} {g : GameForm} {n : ℕ}
    (h_hasStride : HasStride p g n) : ¬IsSolved p g ↔ 0 < n := by
  rw [hasStride_isSolved_iff_zero h_hasStride]
  simp only [ne_iff_gt_iff_ge, zero_le]

theorem hasStride_succ_iff {p : Player} {g : GameForm} {n : ℕ} :
    HasStride p g (n + 1) ↔
    ¬IsSolved p g
    ∧ (∀ g' ∈ moves p g, ∃ k, n ≤ k ∧ HasStride p g' k)
    ∧ (∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n
        ∧ ∃ m, HasStride (-p) g' m ∧ StrideCandidate (-p) g m)
    ∧ (∀ g' ∈ moves (-p) g, ∃ k, k ≤ n + 1 ∧ HasStride p g' k) := by
  constructor
  · intro h; unfold HasStride at h; exact h
  · intro h; unfold HasStride; exact h

@[simp]
theorem strideCandidate_zero_iff {p : Player} {g : GameForm} :
    StrideCandidate p g 0 ↔ IsSolved p g := Iff.rfl

theorem strideCandidate_succ_iff {p : Player} {g : GameForm} {m : ℕ} :
    StrideCandidate p g (m + 1) ↔
    ¬IsSolved p g
    ∧ (∀ g' ∈ moves p g, ∃ k, m ≤ k ∧ HasStride p g' k)
    ∧ (∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' m) := Iff.rfl

/--
A stride is in particular a stride candidate.
-/
theorem hasStride_strideCandidate {p : Player} {g : GameForm} {n : ℕ}
    (h : HasStride p g n) : StrideCandidate p g n := by
  match n with
  | 0 => exact hasStride_eq_zero_iff.mp h
  | n + 1 =>
    obtain ⟨h₁, h₂, ⟨g', hg', hg'_stride, _⟩, _⟩ := hasStride_succ_iff.mp h
    exact ⟨h₁, h₂, g', hg', hg'_stride⟩

/--
If the stride of $G$ is not zero, then every response lowers the stride by at
most one.
-/
theorem hasStride_succ_support {p : Player} {g : GameForm} {n : ℕ}
    (h : HasStride p g (n + 1)) (g' : GameForm) (hg' : g' ∈ moves p g) :
    ∃ k, n ≤ k ∧ HasStride p g' k :=
  (hasStride_succ_iff.mp h).2.1 g' hg'

/--
If the stride of $G$ is not zero, then there exist some response lowering the
stride by exactly one which keeps the opponent's stride candidate.
-/
theorem hasStride_succ_exists_best {p : Player} {g : GameForm} {n : ℕ}
    (h : HasStride p g (n + 1)) :
    ∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n
        ∧ ∃ m, HasStride (-p) g' m ∧ StrideCandidate (-p) g m :=
  (hasStride_succ_iff.mp h).2.2.1

/--
If the stride of $G$ is not zero, then no opponent move raises the stride.
-/
theorem hasStride_succ_support_neg {p : Player} {g : GameForm} {n : ℕ}
    (h : HasStride p g (n + 1)) (g' : GameForm) (hg' : g' ∈ moves (-p) g) :
    ∃ k, k ≤ n + 1 ∧ HasStride p g' k :=
  (hasStride_succ_iff.mp h).2.2.2 g' hg'

theorem hasStride_succ_not_isEnd {p : Player} {g : GameForm} {n : ℕ}
    (h : HasStride p g (n + 1)) : ¬IsEnd p g := by
  have ⟨_, h_mem, _⟩ := hasStride_succ_exists_best h
  exact not_isEnd_of_mem_moves h_mem

/--
If a game has stride, then the value is unique.

This is a workaround for not defining stride as a function to `option ℕ`.
-/
theorem hasStride_unique {p : Player} {g : GameForm} {n k : ℕ}
    (h_n : HasStride p g n) (h_k : HasStride p g k) : n = k := by
  match n, k with
  | 0, 0 => rfl
  | 0, .succ _ => have := (hasStride_isSolved_iff_zero h_k).mp (hasStride_eq_zero_iff.mp h_n); omega
  | .succ _, 0 => have := (hasStride_isSolved_iff_zero h_n).mp (hasStride_eq_zero_iff.mp h_k); omega
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
termination_by g
decreasing_by form_wf

/--
A stride candidate is unique, since it is determined by the strides of the
options.
-/
theorem strideCandidate_unique {p : Player} {g : GameForm} {n k : ℕ}
    (h_n : StrideCandidate p g n) (h_k : StrideCandidate p g k) : n = k := by
  match n, k with
  | 0, 0 => rfl
  | 0, .succ _ => exact absurd h_n h_k.1
  | .succ _, 0 => exact absurd h_k h_n.1
  | .succ n, .succ k =>
    congr 1
    obtain ⟨_, h_n_support, g1, hg1_mem, hg1_stride⟩ := h_n
    obtain ⟨_, h_k_support, g2, hg2_mem, hg2_stride⟩ := h_k
    have ⟨j, hkj, hj_stride⟩ := h_k_support g1 hg1_mem
    have ⟨j', hnj', hj'_stride⟩ := h_n_support g2 hg2_mem
    have h_nj := hasStride_unique hg1_stride hj_stride
    have h_kj' := hasStride_unique hg2_stride hj'_stride
    omega

/--
Helper for building iff lemmas
-/
theorem hasStride_mk_iff {p : Player} (n : ℕ) {k : ℕ} {g : GameForm} (h_stride : HasStride p g n) :
    HasStride p g k ↔ k = n := by
  constructor
  · intro h
    exact hasStride_unique h h_stride
  · intro h
    subst h
    exact h_stride

/--
The good move preserves (-p)-stride: if HasStride p g (n+1) and HasStride (-p)
g r, then the good p-move has (-p)-stride exactly r.
-/
theorem hasStride_good_move_neg_stride {p : Player} {g : GameForm} {n r : ℕ}
    (h : HasStride p g (n + 1))
    (h_r : HasStride (-p) g r) :
    ∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n ∧ HasStride (-p) g' r := by
  have ⟨g1, hg1_mem, hg1_stride_p, m, hg1_stride_neg, h_cand⟩ := hasStride_succ_exists_best h
  rw [strideCandidate_unique h_cand (hasStride_strideCandidate h_r)] at hg1_stride_neg
  exact ⟨g1, hg1_mem, hg1_stride_p, hg1_stride_neg⟩

/--
Opponent moves have stride ≤ n.
-/
theorem hasStride_of_mem_moves_neg {p : Player} {g g' : GameForm} {n : ℕ}
    (hg : HasStride p g n) (hm : g' ∈ moves (-p) g) : ∃ k, k ≤ n ∧ HasStride p g' k := by
  match n with
  | 0 => exact ⟨0, le_refl _, hasStride_eq_zero_iff.mpr (isSolved_of_mem_moves (hasStride_eq_zero_iff.mp hg) hm)⟩
  | .succ n' => exact hasStride_succ_support_neg hg g' hm

/--
A variant of `hasStride_succ_iff` for when the (-p)-stride is known: the good
move then simply has to preserve it.
-/
theorem hasStride_succ_iff' {p : Player} {g : GameForm} {n m : ℕ}
    (h_hasStride_m : HasStride (-p) g m) :
    HasStride p g (n + 1) ↔
    ¬IsSolved p g
    ∧ (∀ g' ∈ moves p g, ∃ k, n ≤ k ∧ HasStride p g' k)
    ∧ (∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n ∧ HasStride (-p) g' m)
    ∧ (∀ g' ∈ moves (-p) g, ∃ k, k ≤ n + 1 ∧ HasStride p g' k) := by
  rw [hasStride_succ_iff]
  constructor <;> intro h <;> rcases h with ⟨h₁, h₂, h₃, h₄⟩
  · exact ⟨h₁, h₂, hasStride_good_move_neg_stride (hasStride_succ_iff.mpr ⟨h₁, h₂, h₃, h₄⟩) h_hasStride_m, h₄⟩
  · obtain ⟨g', hg', hg₁, hg₂⟩ := h₃
    exact ⟨h₁, h₂, ⟨g', hg', hg₁, m, hg₂, hasStride_strideCandidate h_hasStride_m⟩, h₄⟩

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
  | 0 => exact ⟨0, Nat.zero_le _, hasStride_eq_zero_iff.mpr (isSolved_of_mem_moves (hasStride_eq_zero_iff.mp hg) hm)⟩
  | .succ n =>
    have ⟨j, hj, hjs⟩ := hasStride_succ_support hg g' hm
    exact ⟨j, by simpa only [Nat.succ_eq_add_one, add_tsub_cancel_right] using hj, hjs⟩

/--
Build the strides of both players of `g` from their values `n` at `g` and the
strides of the options. This is the interface for rulesets: the hypotheses
are the "race" conditions on the ruleset's stride function at `g`.
-/
theorem hasStride_of_options (g : GameForm) (n : Player → ℕ)
    (h_solved : ∀ q, n q = 0 → IsSolved q g)
    (h_not_solved : ∀ q, n q ≠ 0 → ¬IsSolved q g)
    (h_support : ∀ q, ∀ g' ∈ moves q g, ∃ k, n q ≤ k + 1 ∧ HasStride q g' k)
    (h_best : ∀ q, n q ≠ 0 →
      ∃ g', ∃ (_ : g' ∈ moves q g), HasStride q g' (n q - 1) ∧ HasStride (-q) g' (n (-q)))
    (h_support_neg : ∀ q, ∀ g' ∈ moves (-q) g, ∃ k, k ≤ n q ∧ HasStride q g' k)
    (q : Player) : HasStride q g (n q) := by
  have h_candidate : ∀ q, StrideCandidate q g (n q) := by
    intro q
    by_cases h_zero : n q = 0
    · rw [h_zero]
      exact h_solved q h_zero
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h_zero
      rw [hm]
      refine ⟨h_not_solved q h_zero, ?_, ?_⟩
      · intro g' hg'
        obtain ⟨k, hk, hk_stride⟩ := h_support q g' hg'
        exact ⟨k, by omega, hk_stride⟩
      · obtain ⟨g', hg', hg'_stride, _⟩ := h_best q h_zero
        rw [hm, Nat.succ_sub_one] at hg'_stride
        exact ⟨g', hg', hg'_stride⟩
  by_cases h_zero : n q = 0
  · rw [h_zero]
    exact hasStride_eq_zero_iff.mpr (h_solved q h_zero)
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h_zero
    rw [hm, hasStride_succ_iff]
    refine ⟨h_not_solved q h_zero, ?_, ?_, ?_⟩
    · intro g' hg'
      obtain ⟨k, hk, hk_stride⟩ := h_support q g' hg'
      exact ⟨k, by omega, hk_stride⟩
    · obtain ⟨g', hg', hg'_stride, hg'_neg⟩ := h_best q h_zero
      rw [hm, Nat.succ_sub_one] at hg'_stride
      exact ⟨g', hg', hg'_stride, n (-q), hg'_neg, h_candidate (-q)⟩
    · intro g' hg'
      obtain ⟨k, hk, hk_stride⟩ := h_support_neg q g' hg'
      exact ⟨k, by omega, hk_stride⟩

/-! ### Addition -/

/--
The stride of a sum is the sum of the strides.
-/
theorem hasStride_add {p : Player} {g h : GameForm} {sL_g sL_h sR_g sR_h : ℕ}
    (h_sL_g : HasStride p g sL_g) (h_sL_h : HasStride p h sL_h)
    (h_sR_g : HasStride (-p) g sR_g) (h_sR_h : HasStride (-p) h sR_h) :
    HasStride p (g + h) (sL_g + sL_h) := by
  -- The stride candidate of the sum, for either player. Only strides of
  -- options are needed, so this is available for both players even though
  -- the stride of the sum itself is what we are proving.
  have h_candidate : ∀ (q : Player) {a b a' b' : ℕ},
      HasStride q g a → HasStride q h b → HasStride (-q) g a' → HasStride (-q) h b' →
      StrideCandidate q (g + h) (a + b) := by
    intro q a b a' b' h_a h_b h_a' h_b'
    by_cases h_ab_zero : a + b = 0
    · have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst ha0; subst hb0
      exact isSolved_add (hasStride_eq_zero_iff.mp h_a) (hasStride_eq_zero_iff.mp h_b)
    · obtain ⟨s, hs⟩ : ∃ s, a + b = s + 1 := ⟨a + b - 1, by omega⟩
      rw [hs, strideCandidate_succ_iff]
      refine ⟨?_, ?_, ?_⟩
      · rcases a.eq_zero_or_pos with h_eq | h_pos_a
        · have ⟨b', hb'⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
          subst hb'
          exact not_isSolved_add_right (hasStride_succ_iff.mp h_b).1
        · have ⟨a'', ha''⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
          subst ha''
          exact not_isSolved_add_left (hasStride_succ_iff.mp h_a).1
      · intro g' hg'
        rw [moves_add] at hg'
        simp only [Set.mem_union, Set.mem_image] at hg'
        obtain ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ := hg'
        · have ⟨j, hj, hj_s⟩ := hasStride_of_mem_moves h_a hx
          have ⟨mx, _, hmx_s⟩ := hasStride_of_mem_moves_neg h_a'
              (show x ∈ moves (-(-q)) g by rwa [neg_neg])
          exact ⟨j + b, by omega, hasStride_add hj_s h_b hmx_s h_b'⟩
        · have ⟨j, hj, hj_s⟩ := hasStride_of_mem_moves h_b hx
          have ⟨lx, _, hlx_s⟩ := hasStride_of_mem_moves_neg h_b'
              (show x ∈ moves (-(-q)) h by rwa [neg_neg])
          exact ⟨a + j, by omega, hasStride_add h_a hj_s h_a' hlx_s⟩
      · rcases a.eq_zero_or_pos with h_eq | h_pos_a
        · subst h_eq
          have ⟨b', hb'⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
          subst hb'
          have ⟨h₁, hh1_mem, hh1_p, hh1_neg⟩ := hasStride_good_move_neg_stride h_b h_b'
          refine ⟨g + h₁, add_left_mem_moves_add hh1_mem g, ?_⟩
          have := hasStride_add h_a hh1_p h_a' hh1_neg
          rw [show s = 0 + b' by omega]
          exact this
        · have ⟨a'', ha''⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
          subst ha''
          have ⟨g₁, hg1_mem, hg1_p, hg1_neg⟩ := hasStride_good_move_neg_stride h_a h_a'
          refine ⟨g₁ + h, add_right_mem_moves_add hg1_mem h, ?_⟩
          have := hasStride_add hg1_p h_b hg1_neg h_b'
          rw [show s = a'' + b by omega]
          exact this
  by_cases h_sL_g_sL_h_eq_zero : sL_g + sL_h = 0
  · -- Both strides are zero
    have hg0 : sL_g = 0 := by omega
    have hh0 : sL_h = 0 := by omega
    subst hg0; subst hh0
    exact hasStride_eq_zero_iff.mpr (isSolved_add (hasStride_eq_zero_iff.mp h_sL_g) (hasStride_eq_zero_iff.mp h_sL_h))
  · -- At least one stride is positive
    obtain ⟨s, hs⟩ : ∃ s, sL_g + sL_h = s + 1 := ⟨sL_g + sL_h - 1, by omega⟩
    have h_cand_p := h_candidate p h_sL_g h_sL_h h_sR_g h_sR_h
    rw [hs, strideCandidate_succ_iff] at h_cand_p
    obtain ⟨h_not_solved, h_support, _⟩ := h_cand_p
    have h_cand_neg : StrideCandidate (-p) (g + h) (sR_g + sR_h) :=
      h_candidate (-p) h_sR_g h_sR_h (by rwa [neg_neg]) (by rwa [neg_neg])
    rw [hs, hasStride_succ_iff]
    refine ⟨h_not_solved, h_support, ?_, ?_⟩
    -- (iii): the good move comes from the component with positive stride and
    -- preserves the opponent's stride
    · rcases sL_g.eq_zero_or_pos with h_eq | h_pos_g
      · subst h_eq
        have ⟨sL_h', hsL_h'⟩ : ∃ n, sL_h = n + 1 := ⟨sL_h - 1, by omega⟩
        subst hsL_h'
        have ⟨h₁, hh1_mem, hh1_p, hh1_neg⟩ := hasStride_good_move_neg_stride h_sL_h h_sR_h
        refine ⟨g + h₁, add_left_mem_moves_add hh1_mem g, ?_, sR_g + sR_h, ?_, h_cand_neg⟩
        · have := hasStride_add h_sL_g hh1_p h_sR_g hh1_neg
          rw [show s = 0 + sL_h' by omega]
          exact this
        · exact hasStride_add h_sR_g hh1_neg (by rwa [neg_neg]) (by rwa [neg_neg])
      · have ⟨sL_g', hsL_g'⟩ : ∃ n, sL_g = n + 1 := ⟨sL_g - 1, by omega⟩
        subst hsL_g'
        have ⟨g₁, hg1_mem, hg1_p, hg1_neg⟩ := hasStride_good_move_neg_stride h_sL_g h_sR_g
        refine ⟨g₁ + h, add_right_mem_moves_add hg1_mem h, ?_, sR_g + sR_h, ?_, h_cand_neg⟩
        · have := hasStride_add hg1_p h_sL_h hg1_neg h_sR_h
          rw [show s = sL_g' + sL_h by omega]
          exact this
        · exact hasStride_add hg1_neg h_sR_h (by rwa [neg_neg]) (by rwa [neg_neg])
    -- (iv)
    · intro g' hg'
      rw [moves_add] at hg'
      simp only [Set.mem_union, Set.mem_image] at hg'
      obtain ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ := hg'
      · have ⟨j, hj, hj_s⟩ := hasStride_of_mem_moves_neg h_sL_g hx
        have ⟨mx, _, hmx_s⟩ := hasStride_of_mem_moves h_sR_g hx
        exact ⟨j + sL_h, by omega, hasStride_add hj_s h_sL_h hmx_s h_sR_h⟩
      · have ⟨j, hj, hj_s⟩ := hasStride_of_mem_moves_neg h_sL_h hx
        have ⟨lx, _, hlx_s⟩ := hasStride_of_mem_moves h_sR_h hx
        exact ⟨sL_g + j, by omega, hasStride_add h_sL_g hj_s h_sR_g hlx_s⟩
termination_by (g, h)
decreasing_by form_wf

private theorem hasStride_neg {p : Player} {g : GameForm} {n : ℕ}
    (h_hasStride : HasStride p g n) :
    HasStride (-p) (-g) n := by
  match n with
  | 0 =>
    simp only [hasStride_eq_zero_iff, isSolved_neg_iff] at ⊢ h_hasStride
    exact h_hasStride
  | n + 1 =>
    rw [hasStride_succ_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hasStride_isSolved_iff_zero h_hasStride]
    · simp only [moves_neg, neg_neg, Set.mem_neg, Set.forall_neg_mem]
      intro g' h_g'_mem
      have ⟨k, h1, h2⟩ := hasStride_succ_support h_hasStride g' h_g'_mem
      use k, h1, hasStride_neg h2
    · have ⟨g', h_g'_mem, h1, m, h_m, h_cand⟩ := hasStride_succ_exists_best h_hasStride
      refine ⟨-g', ?_, hasStride_neg h1, m, ?_, ?_⟩
      · simp only [moves_neg, neg_neg, Set.mem_neg]
        exact h_g'_mem
      · exact hasStride_neg h_m
      · match m, h_cand with
        | 0, h_cand =>
          rw [strideCandidate_zero_iff] at h_cand ⊢
          rw [neg_neg, isSolved_neg_iff']
          exact h_cand
        | m + 1, h_cand =>
          rw [strideCandidate_succ_iff] at h_cand ⊢
          obtain ⟨h_cand_not_solved, h_cand_support, g'', h_g''_mem, h_g''⟩ := h_cand
          refine ⟨?_, ?_, -g'', ?_, ?_⟩
          · rw [neg_neg, isSolved_neg_iff']
            exact h_cand_not_solved
          · simp only [neg_neg, moves_neg, Set.mem_neg, Set.forall_neg_mem]
            intro x h_x_mem
            have ⟨k, h_k, h_k_stride⟩ := h_cand_support x h_x_mem
            have := hasStride_neg h_k_stride
            rw [neg_neg] at this
            exact ⟨k, h_k, this⟩
          · simp only [neg_neg, moves_neg, Set.mem_neg]
            exact h_g''_mem
          · exact hasStride_neg h_g''
    · simp only [neg_neg, moves_neg, Set.mem_neg, Set.forall_neg_mem]
      intro g' h_g'_mem
      have ⟨k, h1, h2⟩ := hasStride_succ_support_neg h_hasStride g' h_g'_mem
      use k, h1, hasStride_neg h2
termination_by birthday g
decreasing_by all_goals gameform_birthday

@[simp]
theorem hasStride_neg_iff {p : Player} {g : GameForm} {n : ℕ} :
    HasStride (-p) (-g) n ↔ HasStride p g n := by
  constructor
  · intro h
    have := hasStride_neg h
    rwa [neg_neg, neg_neg] at this
  · exact hasStride_neg

@[simp]
theorem hasStride_neg_iff' {p : Player} {g : GameForm} {n : ℕ} :
    HasStride p (-g) n ↔ HasStride (-p) g n := by
  rw [<-neg_neg p, hasStride_neg_iff, neg_neg]

/-! ### Ordinal sums -/

/--
The stride candidate of an ordinal sum, given the strides of the ordinal sums
with the options of the branch.
-/
private theorem strideCandidate_ordinalSum {p : Player} {x y : GameForm} {l r : ℕ}
    (h_ne_zero : x ≠ 0) (h_l : HasStride p x l) (h_r : HasStride (-p) x r)
    (ih : ∀ y' ∈ moves p y, HasStride p (ordinalSum x y') l) :
    StrideCandidate p (ordinalSum x y) l := by
  match l with
  | 0 => exact isSolved_ordinalSum y h_ne_zero (hasStride_eq_zero_iff.mp h_l)
  | n + 1 =>
    rw [strideCandidate_succ_iff]
    refine ⟨(isSolved_ordinalSum_iff h_ne_zero).not.mpr (hasStride_succ_iff.mp h_l).1, ?_, ?_⟩
    · intro z h_z
      rw [mem_moves_ordinalSum_iff] at h_z
      obtain h_z | ⟨y', h_y', rfl⟩ := h_z
      · exact hasStride_succ_support h_l z h_z
      · exact ⟨n + 1, Nat.le_succ n, ih y' h_y'⟩
    · obtain ⟨x', h_x', h_x'_stride, _⟩ := hasStride_succ_exists_best' h_l h_r
      exact ⟨x', mem_moves_ordinalSum_base y h_x', h_x'_stride⟩

/--
Ordinal sums forget their branch: the strides of `x : y` are the strides of
the base `x`, for every branch `y` whatsoever. The base must be nonzero since
`0 : y = y`.

Together with `hasStride_add` this recovers the strides of Hackenbush trees,
`Σ (ground edge : subtree)`, without any graph argument; see
`Hackenbush.hasStride_groundCount` for the general graph case.
-/
theorem hasStride_ordinalSum {p : Player} {x : GameForm} (y : GameForm) {l r : ℕ}
    (h_ne_zero : x ≠ 0) (h_l : HasStride p x l) (h_r : HasStride (-p) x r) :
    HasStride p (ordinalSum x y) l := by
  match l with
  | 0 =>
    exact hasStride_eq_zero_iff.mpr (isSolved_ordinalSum y h_ne_zero (hasStride_eq_zero_iff.mp h_l))
  | n + 1 =>
    have h_l' : HasStride (-(-p)) x (n + 1) := by rwa [neg_neg]
    have h_candidate : StrideCandidate (-p) (ordinalSum x y) r :=
      strideCandidate_ordinalSum h_ne_zero h_r h_l'
        fun y' h_y' => hasStride_ordinalSum y' h_ne_zero h_r h_l'
    rw [hasStride_succ_iff]
    refine ⟨(isSolved_ordinalSum_iff h_ne_zero).not.mpr (hasStride_succ_iff.mp h_l).1, ?_, ?_, ?_⟩
    · intro z h_z
      rw [mem_moves_ordinalSum_iff] at h_z
      obtain h_z | ⟨y', h_y', rfl⟩ := h_z
      · exact hasStride_succ_support h_l z h_z
      · exact ⟨n + 1, Nat.le_succ n, hasStride_ordinalSum y' h_ne_zero h_l h_r⟩
    · obtain ⟨x', h_x', h_x'_stride, h_x'_stride_neg⟩ := hasStride_succ_exists_best' h_l h_r
      exact ⟨x', mem_moves_ordinalSum_base y h_x', h_x'_stride, r, h_x'_stride_neg, h_candidate⟩
    · intro z h_z
      rw [mem_moves_ordinalSum_iff] at h_z
      obtain h_z | ⟨y', h_y', rfl⟩ := h_z
      · exact hasStride_succ_support_neg h_l z h_z
      · exact ⟨n + 1, le_refl _, hasStride_ordinalSum y' h_ne_zero h_l h_r⟩
termination_by y
decreasing_by form_wf

theorem hasStride_ordinalSum_iff {p : Player} {x : GameForm} (y : GameForm) {l r k : ℕ}
    (h_ne_zero : x ≠ 0) (h_l : HasStride p x l) (h_r : HasStride (-p) x r) :
    HasStride p (ordinalSum x y) k ↔ k = l :=
  hasStride_mk_iff l (hasStride_ordinalSum y h_ne_zero h_l h_r)

/-! ### Integers -/

theorem hasStride_zero (p : Player) : HasStride p 0 0 := by
  simp only [hasStride_eq_zero_iff, isSolved_zero]

@[simp]
theorem hasStride_zero_iff {p : Player} {n : ℕ} : HasStride p 0 n ↔ n = 0 :=
  hasStride_mk_iff 0 (hasStride_zero p)

theorem hasStride_right_natCast (n : ℕ) : HasStride .right n 0 :=
  hasStride_eq_zero_iff.mpr (isSolved_right_natCast n)

@[simp]
theorem hasStride_right_natCast_iff (n : ℕ) {k : ℕ} : HasStride .right n k ↔ k = 0 :=
  hasStride_mk_iff 0 (hasStride_right_natCast n)

theorem hasStride_right_one : HasStride .right 1 0 := by
  rw [<-Form.natCast_one, hasStride_right_natCast_iff]

@[simp]
theorem hasStride_right_one_iff {n : ℕ} : HasStride .right 1 n ↔ n = 0 :=
  hasStride_mk_iff 0 hasStride_right_one

theorem hasStride_left_one : HasStride .left 1 1 := by
  rw [hasStride_succ_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := isSolved_zero_not_mem h
    simp only [leftMoves_one, Set.mem_singleton_iff, not_true_eq_false] at this
  · simp
  · refine ⟨0, by simp, hasStride_zero .left, 0, hasStride_zero _, ?_⟩
    rw [strideCandidate_zero_iff, Player.neg_left]
    exact isSolved_right_one
  · simp

theorem hasStride_left_natCast (n : ℕ) : HasStride .left (n : GameForm.{u}) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    exact hasStride_add ih hasStride_left_one (hasStride_right_natCast n) hasStride_right_one

@[simp]
theorem hasStride_left_natCast_iff (n : ℕ) {k : ℕ} : HasStride .left (n : GameForm.{u}) k ↔ k = n :=
  hasStride_mk_iff n (hasStride_left_natCast n)

theorem hasStride_left_intCast (n : ℤ) :
    HasStride .left ((n : GameForm.{u})) n.toNat := by
  match n with
  | .ofNat n => simp
  | .negSucc n =>
    simp only [Form.intCast_negSucc, Int.toNat_negSucc, hasStride_eq_zero_iff]
    simp [isSolved_add]

@[simp]
theorem hasStride_left_intCast_iff (n : ℤ) {k : ℕ} :
    HasStride .left ((n : GameForm.{u})) k ↔ k = n.toNat :=
  hasStride_mk_iff n.toNat (hasStride_left_intCast n)

@[simp]
theorem hasStride_right_intCast_iff (n : ℤ) {k : ℕ} :
    HasStride .right ((n : GameForm.{u})) k ↔ k = (-n).toNat := by
  rw [<-neg_neg n, Form.intCast_neg, hasStride_neg_iff', Player.neg_right,
      hasStride_left_intCast_iff, neg_neg]

/-! ### Dyadic rationals

Strides of the canonical forms of `1/2 = {0 | 1}` and `3/4 = {1/2 | 1}`.
The latter is the smallest number whose stride only exists because the good
move is required to *preserve* the opponent's stride rather than the
opponent being required to be able to preserve ours: Right's only move from
`3/4` is to `1`, which lowers Left's stride from `2` to `1`.
-/

theorem isSolved_right_half : IsSolved .right !{{0} | {1}} := by
  rw [isSolved_def]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro _
    simp [isEnd_def]
  · intro gp h_isOption
    simp only [isOption_iff_mem_union, leftMoves_ofSets, rightMoves_ofSets, Set.union_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at h_isOption
    obtain rfl | rfl := h_isOption
    · exact isSolved_right_one
    · exact isSolved_zero _

theorem hasStride_left_half : HasStride .left !{{0} | {1}} 1 := by
  rw [hasStride_succ_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := isSolved_zero_not_mem h
    simp at this
  · simp
  · refine ⟨0, by simp, hasStride_zero .left, 0, hasStride_zero _, ?_⟩
    rw [strideCandidate_zero_iff, Player.neg_left]
    exact isSolved_right_half
  · simp only [Player.neg_left, rightMoves_ofSets, Set.mem_singleton_iff, forall_eq]
    exact ⟨1, le_refl _, hasStride_left_one⟩

theorem isSolved_right_threeQuarters : IsSolved .right !{{!{{0} | {1}}} | {1}} := by
  rw [isSolved_def]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro _
    simp [isEnd_def]
  · intro gp h_isOption
    simp only [isOption_iff_mem_union, leftMoves_ofSets, rightMoves_ofSets, Set.union_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at h_isOption
    obtain rfl | rfl := h_isOption
    · exact isSolved_right_one
    · exact isSolved_right_half

theorem hasStride_left_threeQuarters : HasStride .left !{{!{{0} | {1}}} | {1}} 2 := by
  rw [hasStride_succ_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := isSolved_zero_not_mem (isSolved_of_mem_moves h (show !{{0} | {1}} ∈ moves .left _ by simp))
    simp at this
  · simp only [leftMoves_ofSets, Set.mem_singleton_iff, forall_eq]
    exact ⟨1, le_refl _, hasStride_left_half⟩
  · refine ⟨!{{0} | {1}}, by simp, hasStride_left_half, 0, ?_, ?_⟩
    · rw [Player.neg_left]
      exact hasStride_eq_zero_iff.mpr isSolved_right_half
    · rw [strideCandidate_zero_iff, Player.neg_left]
      exact isSolved_right_threeQuarters
  · simp only [Player.neg_left, rightMoves_ofSets, Set.mem_singleton_iff, forall_eq]
    exact ⟨1, by omega, hasStride_left_one⟩

/-! ### Outcomes -/

private theorem hasStride_winsGoingFirst {p : Player} {g : GameForm} {l r : ℕ}
    (h_l : HasStride p g l) (h_r : HasStride (-p) g r) (h_le : l ≤ r) :
    WinsGoingFirst p g := by
  match l with
  | 0 => exact isSolved_winsGoingFirst (hasStride_eq_zero_iff.mp h_l)
  | .succ sL_g =>
    have ⟨sR_g, h_sR_g⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    subst h_sR_g
    have ⟨gL, h_gL_mem, h_gL_stride_L, h_gL_stride_R⟩ := hasStride_good_move_neg_stride h_l h_r
    apply winsGoingFirst_of_moves
    use gL, h_gL_mem
    rw [not_winsGoingFirst_iff]
    constructor
    · rw [isEndLike_iff_isEnd]
      exact hasStride_succ_not_isEnd h_gL_stride_R
    · intro gLR h_gLR_mem
      rw [neg_neg]
      match sL_g with
      | 0 =>
        exact isSolved_winsGoingFirst
          (isSolved_of_isOption (hasStride_eq_zero_iff.mp h_gL_stride_L) (IsOption.of_mem_moves h_gLR_mem))
      | .succ sL_g =>
        have ⟨sL_gLR, h_sL_gLR, h_gLR_strideL⟩ := hasStride_succ_support_neg h_gL_stride_L gLR h_gLR_mem
        have ⟨sR_gLR, h_sR_gLR, h_gLR_strideR⟩ := hasStride_succ_support h_gL_stride_R gLR h_gLR_mem
        have h_le' : sL_gLR ≤ sR_gLR := by omega
        exact hasStride_winsGoingFirst h_gLR_strideL h_gLR_strideR h_le'
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
  · intro gL h_gL_mem
    obtain ⟨sL_gL, h_sL_gL, h_gL_strideL⟩ := hasStride_of_mem_moves h_l h_gL_mem
    have ⟨sR_gL, h_sR_gL, h_gL_strideR⟩ : ∃ sR_gL, sR_gL ≤ r ∧ HasStride (-p) gL sR_gL := by
      match r with
      | 0 =>
        exact ⟨0, le_refl _, hasStride_eq_zero_iff.mpr (isSolved_of_mem_moves (hasStride_eq_zero_iff.mp h_r) h_gL_mem)⟩
      | .succ r' =>
        exact hasStride_succ_support_neg h_r gL (by rw [neg_neg]; exact h_gL_mem)
    have h_le : sR_gL ≤ sL_gL := by omega
    exact hasStride_winsGoingFirst h_gL_strideR (by rwa [neg_neg]) h_le

/--
If a game has both strides, then they determine who wins going first.
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
If a game has both strides, then they determine the outcome.
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
If a game has both strides, then they determine the outcome.
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
Games with the same strides have the same outcome.
-/
theorem misereOutcome_eq_of_hasStride {g h : GameForm} {l r : ℕ}
    (h_lg : HasStride .left g l) (h_rg : HasStride .right g r)
    (h_lh : HasStride .left h l) (h_rh : HasStride .right h r) :
    MisereOutcome g = MisereOutcome h := by
  have h_rg' : HasStride (-Player.left) g r := h_rg
  have h_rh' : HasStride (-Player.left) h r := h_rh
  have h_lg' : HasStride (-Player.right) g l := h_lg
  have h_lh' : HasStride (-Player.right) h l := h_lh
  obtain h_lt | h_eq | h_gt := Nat.lt_trichotomy l r
  · rw [(hasStride_misereOutcome_iff_lt h_lg h_rg').mpr h_lt,
      (hasStride_misereOutcome_iff_lt h_lh h_rh').mpr h_lt]
  · rw [(hasStride_misereOutcome_iff_eq h_lg h_rg').mpr h_eq,
      (hasStride_misereOutcome_iff_eq h_lh h_rh').mpr h_eq]
  · rw [(hasStride_misereOutcome_iff_lt h_rg h_lg').mpr h_gt,
      (hasStride_misereOutcome_iff_lt h_rh h_lh').mpr h_gt]

/--
If a game has both strides, then it is $\mathscr{P}$-free.
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

private instance hasStride_closedUnderAdd :
    ClosedUnderAdd (fun g : GameForm => ∀ p, ∃ n, GameForm.HasStride p g n) where
  has_add x y hx hy p := by
    obtain ⟨a, ha⟩ := hx p
    obtain ⟨a', ha'⟩ := hx (-p)
    obtain ⟨b, hb⟩ := hy p
    obtain ⟨b', hb'⟩ := hy (-p)
    exact ⟨a + b, GameForm.hasStride_add ha hb ha' hb'⟩

theorem ClosedUnderAdd.closure_has_stride_aux {R : Type u} [Ruleset R] (p : Player) {g : GameForm}
    (stride : R → Player → ℕ)
    (hasStride : (r : R) → (p : Player) → GameForm.HasStride p (Ruleset.toGameForm r) (stride r p))
    (h_g : ClosedUnderAdd.closure (Ruleset.Forms R) g)
    : ∃ n, GameForm.HasStride p g n := by
  refine ClosedUnderAdd.closure_min (A := Ruleset.Forms R)
      (B := fun g => ∀ p, ∃ n, GameForm.HasStride p g n) ?_ g h_g p
  intro x hx q
  obtain ⟨r, h_r⟩ := Ruleset.Forms.exists hx
  refine ⟨stride r q, ?_⟩
  rw [h_r]
  exact hasStride r q

theorem ClosedUnderAdd.closure_mk_with_strides_aux {A : GameForm → Prop}
    (mk_stride_other_zero : (p : Player) → (n : ℕ) → ∃ g, A g ∧ HasStride p g n ∧ HasStride (-p) g 0)
    (l r : ℕ) :
    ∃ t, ClosedUnderAdd.closure A t ∧ HasStride .left t l ∧ HasStride .right t r := by
  obtain ⟨t₁, ht₁_A, ht₁_l, ht₁_r⟩ := mk_stride_other_zero .left l
  obtain ⟨t₂, ht₂_A, ht₂_r, ht₂_l⟩ := mk_stride_other_zero .right r
  refine ⟨t₁ + t₂, ClosedUnderAdd.add_mem_closure
      (ClosedUnderAdd.mem_closure_of_mem ht₁_A) (ClosedUnderAdd.mem_closure_of_mem ht₂_A),
      ?_, ?_⟩
  · have := hasStride_add ht₁_l ht₂_l ht₁_r ht₂_r
    simpa only [add_zero] using this
  · have := hasStride_add ht₁_r ht₂_r ht₁_l ht₂_l
    simpa only [zero_add] using this

private theorem ClosedUnderAdd.closure_has_stride {A : GameForm → Prop} [Strided A]
    (p : Player) {g : GameForm} (h_g : ClosedUnderAdd.closure A g) : ∃ n, HasStride p g n := by
  refine ClosedUnderAdd.closure_min (A := A)
      (B := fun g => ∀ p, ∃ n, GameForm.HasStride p g n) ?_ g h_g p
  intro x hx q
  exact Strided.has_stride q hx

instance {A : GameForm → Prop} [Strided A] : Strided (ClosedUnderAdd.closure A) where
  mk_with_strides l r := by
    obtain ⟨g, h1, h2, h3⟩ := Strided.mk_with_strides (A := A) l r
    exact ⟨g, ClosedUnderAdd.mem_closure_of_mem h1, h2, h3⟩
  has_stride := ClosedUnderAdd.closure_has_stride

section Quotients

variable {A : GameForm → Prop} [Strided A]

theorem stride_diff_eq_of_misereEQ
    {g h : GameForm}
    (h_eq : g =m A h)
    {sL_g sR_g sL_h sR_h : ℕ}
    (h_ng : HasStride .left g sL_g) (h_rg : HasStride .right g sR_g)
    (h_nh : HasStride .left h sL_h) (h_rh : HasStride .right h sR_h) :
    (sL_g : ℤ) - (sR_g : ℤ) = (sL_h : ℤ) - (sR_h : ℤ) := by
  -- Construct a test game t with left stride rg and right stride ng.
  -- Then g + t has equal left and right strides (both ng + rg), giving outcome
  -- N.
  -- Since g =m A h, h + t also has outcome N, forcing nh + rg = rh + ng.
  obtain ⟨t, ht_A, ht_l, ht_r⟩ := Strided.mk_with_strides (A := A) sR_g sL_g
  have h_outcome_g : MisereOutcome (g + t) = .N := by
    rw [hasStride_misereOutcome_iff_eq
         (hasStride_add h_ng ht_l h_rg ht_r)
         (hasStride_add h_rg ht_r h_ng ht_l)]
    omega
  have h_eq_t := (h_eq t ht_A).symm
  rw [h_outcome_g, hasStride_misereOutcome_iff_eq
       (hasStride_add h_nh ht_l h_rh ht_r)
       (hasStride_add h_rh ht_r h_nh ht_l)] at h_eq_t
  omega

/-
Two games with the same stride difference are misère equivalent.
-/
theorem misereEQ_of_stride_diff_eq
    {g h : GameForm}
    {sL_g sR_g sL_h sR_h : ℕ}
    (h_ng : HasStride .left g sL_g) (h_rg : HasStride .right g sR_g)
    (h_nh : HasStride .left h sL_h) (h_rh : HasStride .right h sR_h)
    (h_diff : (sL_g : ℤ) - (sR_g : ℤ) = (sL_h : ℤ) - (sR_h : ℤ)) :
    g =m A h := by
  intro t ht
  obtain ⟨sL_t, h_sL_t⟩ := Strided.has_stride .left ht
  obtain ⟨sR_t, h_sR_t⟩ := Strided.has_stride .right ht
  have h_add1 := hasStride_add h_ng h_sL_t h_rg h_sR_t
  have h_add2 := hasStride_add h_rg h_sR_t h_ng h_sL_t
  have h_add3 := hasStride_add h_nh h_sL_t h_rh h_sR_t
  have h_add4 := hasStride_add h_rh h_sR_t h_nh h_sL_t

  have h_outcome1 := hasStride_misereOutcome_iff_eq h_add1 h_add2
  have h_outcome2 := hasStride_misereOutcome_iff_eq h_add3 h_add4
  have h_outcome3 := hasStride_misereOutcome_iff_lt h_add1 h_add2
  have h_outcome4 := hasStride_misereOutcome_iff_lt h_add3 h_add4
  have h_outcome5 : MisereOutcome (g + t) = .R ↔ sL_g + sL_t > sR_g + sR_t :=
    hasStride_misereOutcome_iff_ge h_add1 h_add2
  have h_outcome6 : MisereOutcome (h + t) = .R ↔ sL_h + sL_t > sR_h + sR_t :=
    hasStride_misereOutcome_iff_ge h_add3 h_add4

  grind only

/--
The stride difference characterises misère equivalence for strided games.
-/
theorem misereEQ_iff_stride_diff_eq
    {g h : GameForm}
    {ng rg nh rh : ℕ}
    (h_ng : HasStride .left g ng) (h_rg : HasStride .right g rg)
    (h_nh : HasStride .left h nh) (h_rh : HasStride .right h rh) :
    (g =m A h) ↔ ((ng : ℤ) - (rg : ℤ) = (nh : ℤ) - (rh : ℤ)) :=
  ⟨fun heq => stride_diff_eq_of_misereEQ (A := A) heq h_ng h_rg h_nh h_rh,
   fun hdiff => misereEQ_of_stride_diff_eq h_ng h_rg h_nh h_rh hdiff⟩

/--
Modulo a strided class, an ordinal sum with a nonzero strided base is equal
to its base, whatever the branch. This is the misère counterpart of the colon
principle.
-/
theorem ordinalSum_misereEQ {x : GameForm} (y : GameForm) {l r : ℕ} (h_ne_zero : x ≠ 0)
    (h_l : HasStride .left x l) (h_r : HasStride .right x r) : ordinalSum x y =m A x :=
  misereEQ_of_stride_diff_eq (hasStride_ordinalSum y h_ne_zero h_l h_r)
    (hasStride_ordinalSum y h_ne_zero h_r h_l) h_l h_r rfl

/-
If the stride difference of g is ≤ that of h (as integers), then g ≥m A h.
Lower stride diff means better for Left, so higher MisereOutcome.
-/
theorem misereGE_of_stride_diff_le
    {g h : GameForm}
    {sL_g sR_g sL_h sR_h : ℕ}
    (h_sL_g : HasStride .left g sL_g) (h_sR_g : HasStride .right g sR_g)
    (h_sL_h : HasStride .left h sL_h) (h_sR_h : HasStride .right h sR_h)
    (h_le : (sL_g : ℤ) - (sR_g : ℤ) ≤ (sL_h : ℤ) - (sR_h : ℤ)) :
    g ≥m A h := by
  intro x hx
  -- By hasStride_add: g+x has strides (ng+lx, rg+rx), h+x has strides (nh+lx,
  -- rh+rx).
  obtain ⟨sL_x, h_sL_x⟩ : ∃ lx, HasStride Player.left x lx := Strided.has_stride .left hx
  obtain ⟨sR_x, h_sR_x⟩ : ∃ rx, HasStride Player.right x rx := Strided.has_stride .right hx
  have h_gx : HasStride Player.left (g + x) (sL_g + sL_x) := hasStride_add h_sL_g h_sL_x h_sR_g h_sR_x
  have h_rx : HasStride Player.right (g + x) (sR_g + sR_x) := hasStride_add h_sR_g h_sR_x h_sL_g h_sL_x
  have h_hx : HasStride Player.left (h + x) (sL_h + sL_x) := hasStride_add h_sL_h h_sL_x h_sR_h h_sR_x
  have h_rx' : HasStride Player.right (h + x) (sR_h + sR_x) := hasStride_add h_sR_h h_sR_x h_sL_h h_sL_x
  have h_outcome_gx :
      MisereOutcome (g + x) =
      if sL_g + sL_x < sR_g + sR_x then .L
      else if sL_g + sL_x = sR_g + sR_x then .N
      else .R := by
    have h1 := hasStride_misereOutcome_iff_lt h_gx h_rx
    have h2 := hasStride_misereOutcome_iff_eq h_gx h_rx
    have h3 := hasStride_misereOutcome_iff_lt h_rx h_gx
    have h4 := hasStride_misereOutcome_iff_eq h_rx h_gx
    simp only [Outcome.ofPlayer_left, Outcome.ofPlayer_right] at h1 h2 h3 h4
    grind only
  have h_outcome_hx : MisereOutcome (h + x) = if sL_h + sL_x < sR_h + sR_x then .L else if sL_h + sL_x = sR_h + sR_x then .N else .R := by
    have h_outcome_hx : MisereOutcome (h + x) = .L ↔ sL_h + sL_x < sR_h + sR_x := by
      convert hasStride_misereOutcome_iff_lt h_hx h_rx' using 1
    have h_outcome_hx' : MisereOutcome (h + x) = .N ↔ sL_h + sL_x = sR_h + sR_x :=
      hasStride_misereOutcome_iff_eq h_hx h_rx'
    have h_outcome_hx'' : MisereOutcome (h + x) = .R ↔ sL_h + sL_x > sR_h + sR_x := by
      convert hasStride_misereOutcome_iff_lt ( p := .right ) h_rx' h_hx using 1
    grind only
  split_ifs at *
    <;> simp_all +decide only [tsub_le_iff_right, lt_self_iff_false, not_false_eq_true, ge_iff_le]
  · grind only
  · omega
  · omega

/--
The misère quotient of a strided class is totally ordered. This follows from
the fact that the ordering is determined by stride differences.
-/
theorem misereQuotient_linearOrder (a b : MisereQuotient A) : a ≤ b ∨ b ≤ a := by
  have ha : A ↑(Form.MisereQuotient.out a) := (Form.MisereQuotient.out a).prop
  have hb : A ↑(Form.MisereQuotient.out b) := (Form.MisereQuotient.out b).prop
  obtain ⟨la, hla⟩ := Strided.has_stride (A := A) .left ha
  obtain ⟨ra, hra⟩ := Strided.has_stride (A := A) .right ha
  obtain ⟨lb, hlb⟩ := Strided.has_stride (A := A) .left hb
  obtain ⟨rb, hrb⟩ := Strided.has_stride (A := A) .right hb
  rcases le_total ((lb : ℤ) - rb) ((la : ℤ) - ra) with h | h
  · exact Or.inl (Form.MisereQuotient.out_le_out.mpr (misereGE_of_stride_diff_le hlb hrb hla hra h))
  · exact Or.inr (Form.MisereQuotient.out_le_out.mpr (misereGE_of_stride_diff_le hla hra hlb hrb h))

/--
The stride difference of a game in a strided class `A`. This is the left stride
minus the right stride, as an integer.
-/
noncomputable def Strided.strideDiff
    (g : GameForm) (hg : A g) : ℤ :=
  ((Strided.has_stride (A := A) .left hg).choose : ℤ) -
  ((Strided.has_stride (A := A) .right hg).choose : ℤ)

/--
The stride difference is well-defined regardless of which stride witnesses are
used.
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
  exact stride_diff_eq_of_misereEQ heq hlg hrg hlh hrh

/--
The stride difference function on the misère quotient, defined via
representative. This is well-defined because misère equivalent games have the
same stride difference.
-/
noncomputable def MisereQuotient.strideDiff : MisereQuotient A → ℤ := by
  apply Quotient.lift (fun (g : {g : GameForm // A g}) => Strided.strideDiff g g.prop)
  intro g h heq
  unfold MisereSetoid at heq
  exact Strided.strideDiff_eq_of_misereEQ g.prop h.prop heq

theorem MisereQuotient.strideDiff_mk (g : GameForm) (hg : A g) :
    strideDiff (MisereQuotient.mk ⟨g, hg⟩) = Strided.strideDiff g hg := by
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
The stride difference function on the quotient is surjective: for any integer
`d`, there is a game in `A` with stride difference `d`.
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
  use Form.MisereQuotient.mk ⟨t, ht_A⟩
  rw [MisereQuotient.strideDiff_mk]
  exact strideDiff_eq ht_l ht_r

/--
The misère quotient of a strided class is equivalent to the integers. The
equivalence sends each equivalence class to its stride difference.
-/
noncomputable def MisereQuotient.stridedEquivInt : MisereQuotient A ≃ ℤ :=
  Equiv.ofBijective MisereQuotient.strideDiff
    ⟨MisereQuotient.strideDiff_injective, MisereQuotient.strideDiff_surjective⟩

/--
If `g ≥m A h` then the stride difference of `g` is `≤` that of `h`. The
converse of `misereGE_of_stride_diff_le`.
-/
theorem stride_diff_le_of_misereGE
    {g h : GameForm}
    (h_ge : g ≥m A h)
    {ng rg nh rh : ℕ}
    (h_ng : HasStride .left g ng) (h_rg : HasStride .right g rg)
    (h_nh : HasStride .left h nh) (h_rh : HasStride .right h rh) :
    (ng : ℤ) - (rg : ℤ) ≤ (nh : ℤ) - (rh : ℤ) := by
  by_contra h_lt
  push_neg at h_lt
  have h_ge' : h ≥m A g :=
    misereGE_of_stride_diff_le h_nh h_rh h_ng h_rg (Int.le_of_lt h_lt)
  have h_eq : g =m A h := MisereEq.of_antisymm h_ge h_ge'
  have h_eq_diff := stride_diff_eq_of_misereEQ  h_eq h_ng h_rg h_nh h_rh
  omega

/--
Misère GE is equivalent to stride difference inequality.
-/
theorem misereGE_iff_stride_diff_le
    {g h : GameForm}
    {ng rg nh rh : ℕ}
    (h_ng : HasStride .left g ng) (h_rg : HasStride .right g rg)
    (h_nh : HasStride .left h nh) (h_rh : HasStride .right h rh) :
    (g ≥m A h) ↔ ((ng : ℤ) - (rg : ℤ) ≤ (nh : ℤ) - (rh : ℤ)) :=
  ⟨fun hge => stride_diff_le_of_misereGE hge h_ng h_rg h_nh h_rh,
   fun hle => misereGE_of_stride_diff_le h_ng h_rg h_nh h_rh hle⟩

/--
The ordering on the misère quotient corresponds to `≥` on stride differences:
`mk A g hg ≤ mk A h hh` iff `strideDiff A g hg ≥ strideDiff A h hh`.
-/
theorem MisereQuotient.mk_le_iff_strideDiff
    (g h : GameForm) (hg : A g) (hh : A h) :
    MisereQuotient.mk ⟨g, hg⟩ ≤ MisereQuotient.mk ⟨h, hh⟩ ↔
      Strided.strideDiff g hg ≥ Strided.strideDiff h hh := by
  obtain ⟨lg, hlg⟩ := Strided.has_stride (A := A) .left hg
  obtain ⟨rg, hrg⟩ := Strided.has_stride (A := A) .right hg
  obtain ⟨lh, hlh⟩ := Strided.has_stride (A := A) .left hh
  obtain ⟨rh, hrh⟩ := Strided.has_stride (A := A) .right hh
  rw [strideDiff_eq hlg hrg, strideDiff_eq hlh hrh, Form.MisereQuotient.mk_le_mk]
  constructor
  · intro hge
    exact stride_diff_le_of_misereGE hge hlh hrh hlg hrg
  · intro hle
    exact misereGE_of_stride_diff_le hlh hrh hlg hrg hle

theorem MisereQuotient.le_iff_strideDiff_ge (a b : MisereQuotient A) :
    a ≤ b ↔ MisereQuotient.strideDiff a ≥ MisereQuotient.strideDiff b := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
    simp only [MisereQuotient.strideDiff, Quotient.lift_mk]
    exact mk_le_iff_strideDiff a b a.prop b.prop

/--
The misère quotient ordering via the integer equivalence: `a ≤ b` iff the image
of `a` under the equivalence is ≥ the image of `b`. Equivalently, the
equivalence is an order-reversing bijection.
-/
theorem MisereQuotient.le_iff_equiv_ge (a b : MisereQuotient A) :
    a ≤ b ↔ MisereQuotient.stridedEquivInt a ≥ MisereQuotient.stridedEquivInt b := by
  exact MisereQuotient.le_iff_strideDiff_ge a b

end Quotients

end GameForm
