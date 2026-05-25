/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.GameGraph
public import CombinatorialGames.Misere.Stride
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Cases

open GameForm

public section

namespace Shove

/-!
# Shove

Shove is played on a horizonatl strip of squares, each square is either empty or occupied by a
Left or Right piece (see `Piece`). In their turn player chooses one of their pieces and moves it
and everything to the left of it (not even necessarily adjacent) one square to the left.
Pieces can fall of the left side of the strip and are removed.
-/

inductive Piece
  | none
  | left
  | right
  deriving DecidableEq

def Piece.ofPlayer : Player → Piece
  | .left => .left
  | .right => .right

@[simp]
theorem Piece.ofPlayer_ne_none (p : Player) : Piece.ofPlayer p ≠ Piece.none := by
  cases p <;> simp [Piece.ofPlayer]

@[simp]
theorem Piece.none_ne_ofPlayer (p : Player) : Piece.none ≠ Piece.ofPlayer p := by
  cases p <;> simp [Piece.ofPlayer]

theorem Piece.ofPlayer_injective : Function.Injective Piece.ofPlayer := by
  intro p q h; cases p <;> cases q <;> simp_all [Piece.ofPlayer]

theorem Piece.eq_none_of_ne_ofPlayer {x : Piece} (hl : x ≠ .ofPlayer .left) (hr : x ≠ .ofPlayer .right) :
    x = .none := by
  cases x <;> simp_all [Piece.ofPlayer]

theorem Piece.ne_none_of_ofPlayer {p : Player} {x : Piece} (h : x = Piece.ofPlayer p) : x ≠ .none := by
  rw [h]
  exact ofPlayer_ne_none p

end Shove

/--
Shove position is encoded as a function from position on a strip (leftmost one being 0) to the piece
that is at that position.

Boards must have finite support (only finitely many occupied squares) for the game to be
well-founded.
-/
structure Shove where
  board : ℕ → Shove.Piece
  finite_support : ∃ N, ∀ n, N ≤ n → board n = .none

namespace Shove

@[ext]
theorem ext {s t : Shove} (h : ∀ n, s.board n = t.board n) : s = t := by
  cases s; cases t; simp only [mk.injEq]; funext n; exact h n

/--
Push piece at position `n`: everything at positions 0..n shifts one square to the left.
The piece at position 0 falls off the board, position n becomes empty,
and positions above n are unchanged.
-/
def push_on (s : Shove) (n : ℕ) : Shove where
  board := fun i =>
    if i < n then s.board (i + 1)
    else if i = n then Piece.none
    else s.board i
  finite_support := by
    obtain ⟨N, hN⟩ := s.finite_support
    exact ⟨N, fun m hm => by
      split_ifs with h1 h2
      · exact hN _ (by omega)
      · rfl
      · exact hN _ hm⟩

@[simp]
theorem push_on_lt (s : Shove) {n i : ℕ} (h : i < n) :
    (s.push_on n).board i = s.board (i + 1) := by
  unfold push_on; simp only [h, ↓reduceIte]

@[simp]
theorem push_on_eq (s : Shove) (n : ℕ) :
    (s.push_on n).board n = .none := by
  unfold push_on; simp only [lt_self_iff_false, ↓reduceIte]

@[simp]
theorem push_on_gt (s : Shove) {n i : ℕ} (h : n < i) :
    (s.push_on n).board i = s.board i := by
  unfold push_on; simp only [Nat.not_lt_of_gt h, ↓reduceIte, Nat.ne_of_gt h]

protected def moves : Player → Shove → Set Shove :=
  fun p s ↦ push_on s '' {n : ℕ | s.board n = Piece.ofPlayer p}

theorem mem_moves_iff (p : Player) (s s' : Shove) :
    s' ∈ Shove.moves p s ↔ ∃ n, s.board n = Piece.ofPlayer p ∧ s' = s.push_on n := by
  simp only [Shove.moves, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩

def _root_.GameGraph.shove : GameGraph Shove where
  moves := Shove.moves

/-! ### Weight measure for well-foundedness -/

/--
The weight of a board is the sum of (i + 1) for each non-empty position i.
This is finite because of the finite support condition, and strictly decreases
with each push operation.
-/
noncomputable def weight (s : Shove) : ℕ :=
  ∑ i ∈ Finset.range s.finite_support.choose,
    if s.board i = .none then 0 else i + 1

theorem weight_eq_of_bound (s : Shove) (N : ℕ) (hN : ∀ n, N ≤ n → s.board n = .none) :
    s.weight = ∑ i ∈ Finset.range N, if s.board i = .none then 0 else i + 1 := by
  have h_weight_def :
      s.weight =
      ∑ i ∈ Finset.range (max (s.finite_support.choose) N),
      (if s.board i = .none then 0 else i + 1) := by
    refine' Finset.sum_subset _ _
      <;> intro i hi <;> simp_all only [Finset.mem_range, lt_sup_iff, true_or]
    grind only [Exists.choose_spec]
  cases max_cases (s.finite_support.choose) N
    <;> simp_all only [sup_of_le_left, sup_eq_left, and_self]
  rw [←Finset.sum_range_add_sum_Ico _ ‹_›];
  simpa using fun i hi₁ hi₂ => hN i hi₁

theorem support_exists (s : Shove) (n : ℕ) :
    ∃ N, ∀ m ≥ N, s.board m = .none ∧ (s.push_on n).board m = .none := by
  have ⟨N, hN⟩ := s.finite_support
  use N + n + 1
  intro m hm
  refine ⟨hN m (by omega),  ?_⟩
  rw [Shove.push_on_gt s (by omega)]
  exact hN m (by omega)

theorem weight_eq (s : Shove) (n : ℕ) :
    s.weight =
    ∑ i ∈ Finset.range ((support_exists s n).choose), (if s.board i = .none then 0 else i + 1) := by
  apply Shove.weight_eq_of_bound s (support_exists s n).choose
  intro m hm
  exact ((support_exists s n).choose_spec m hm).left

theorem push_on_weight_eq (s : Shove) (n : ℕ) :
    (s.push_on n).weight =
    ∑ i ∈ Finset.range ((support_exists s n).choose),
    (if (s.push_on n).board i = .none then 0 else i + 1) := by
    apply Shove.weight_eq_of_bound (s.push_on n) (support_exists s n).choose
    intro m hm
    exact ((support_exists s n).choose_spec m hm).right

theorem weight_push_lt (s : Shove) (n : ℕ) (hn : s.board n ≠ .none) :
    (s.push_on n).weight < s.weight := by
  have h_diff :
      ∑ i ∈ Finset.range ((support_exists s n).choose), (if s.board i = .none then 0 else i + 1) =
      ∑ i ∈ Finset.range n, (if s.board i = .none then 0 else i + 1)
      + (n + 1)
      + ∑ i ∈ Finset.Ico (n + 1) ((support_exists s n).choose), (if s.board i = .none then 0 else i + 1) := by
    rw [← Finset.sum_range_add_sum_Ico _ ( show n + 1 ≤ (support_exists s n).choose from _ )];
    · simp [Finset.sum_range_succ, hn]
    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge fun h => hn <| (support_exists s n).choose_spec n h |>.1)

  have h_diff_push' :
      ∑ i ∈ Finset.range ((support_exists s n).choose), (if (s.push_on n).board i = .none then 0 else i + 1) ≤
      ∑ i ∈ Finset.range n, (if (s.push_on n).board i = .none then 0 else i + 1)
      + ∑ i ∈ Finset.Ico (n + 1) ((support_exists s n).choose),
        (if (s.push_on n).board i = .none then 0 else i + 1) := by
    by_cases h : n < (support_exists s n).choose
    · rw [←Finset.sum_range_add_sum_Ico _ (by omega : n + 1 ≤ (support_exists s n).choose)]
      simp [Finset.sum_range_succ]
    · grind only [Exists.choose_spec]

  have h_diff_push :
      ∑ i ∈ Finset.range ((support_exists s n).choose), (if (s.push_on n).board i = .none then 0 else i + 1) ≤
      ∑ i ∈ Finset.range n, (if s.board (i + 1) = .none then 0 else i + 1)
      + ∑ i ∈ Finset.Ico (n + 1) ((support_exists s n).choose), (if s.board i = .none then 0 else i + 1) := by
    apply le_trans h_diff_push'
    apply add_le_add
    · apply Finset.sum_le_sum
      intro i hi
      rw [Shove.push_on]
      simp_all only [ne_eq, ge_iff_le, Finset.mem_range, ↓reduceIte, Std.le_refl]
    · apply Finset.sum_le_sum
      intro i hi
      rw [Shove.push_on_gt]
      simp_all only [ne_eq, ge_iff_le, Finset.mem_Ico, Order.add_one_le_iff]

  have h_diff_push :
      ∑ i ∈ Finset.range n, (if s.board (i + 1) = .none then 0 else i + 1) ≤
      ∑ i ∈ Finset.range (n + 1), (if s.board i = .none then 0 else i + 1) - 1 := by
    rw [Finset.sum_range_succ']
    split_ifs with h'
    · apply Nat.le_sub_one_of_lt
      apply Finset.sum_lt_sum
      · grind only [Exists.choose_spec]
      · use n - 1
        constructor
        · rw [Finset.mem_range]
          refine (Nat.sub_lt (Nat.pos_of_ne_zero ?_) zero_lt_one)
          intro h_absurd; subst h_absurd
          exact hn h'
        · cases n
          · exfalso; exact hn h'
          · simp_all only [ne_eq, ge_iff_le, add_tsub_cancel_right, ↓reduceIte,
                           lt_add_iff_pos_right, zero_lt_one]
    · exact Finset.sum_le_sum fun _ _ => by split_ifs <;> omega

  simp_all [Finset.sum_range_succ]

  have := Shove.weight_eq s n
  have := Shove.push_on_weight_eq s n
  omega

theorem weight_lt_of_mem_move (p : Player) (s s' : Shove)
    (h_mem : s' ∈ GameGraph.shove.moves p s) :
    s'.weight < s.weight := by
  obtain ⟨n, hn₁, hn₂⟩ := (Shove.mem_moves_iff p s s').mp h_mem
  convert Shove.weight_push_lt s n _ using 1
  · rw [hn₂]
  · subst hn₂
    simp_all only [ne_eq, Piece.ofPlayer_ne_none, not_false_eq_true]

instance : GameGraph.IsWellFounded GameGraph.shove where
  wf := by
    refine { wf := WellFounded.intro ?_ }
    intro s
    induction' n : s.weight using Nat.strong_induction_on with n ih generalizing s
    refine' ⟨ _, fun s' hs' => _ ⟩
    refine ih _ ?_ _ rfl
    obtain ⟨ p, hp ⟩ := hs'
    have := Shove.weight_lt_of_mem_move p s s' hp
    omega

protected noncomputable def toGameForm : Shove → GameForm := GameGraph.toForm (g := GameGraph.shove)

/-! ### Relating board moves to game form moves -/

@[simp]
theorem moves_toGameForm (p : Player) (s : Shove) :
    Form.moves p s.toGameForm = Shove.toGameForm '' (Shove.moves p s) := by
  simp [Shove.toGameForm, GameGraph.shove]

theorem toGameForm_zero_iff (g : Shove) : (g.toGameForm = 0) ↔ (∀ n, g.board n = .none) := by
  constructor <;> intro h;
  · intro n
    by_contra h_contra
    have h_moves : Shove.moves .left g ≠ ∅ ∨ Shove.moves .right g ≠ ∅ := by
      cases h : g.board n
        <;> simp_all only [reduceCtorEq, not_true_eq_false, not_false_eq_true, Shove.moves,
                           ne_eq, Set.image_eq_empty]
      · exact Or.inl (Set.Nonempty.ne_empty ⟨n, h⟩)
      · exact Or.inr (Set.Nonempty.ne_empty ⟨n, h⟩)
    cases h_moves <;> simp_all [Set.ext_iff]
    · obtain ⟨x, hx⟩ := ‹_›
      have := Shove.moves_toGameForm Player.left g
      simp_all [Set.ext_iff]
    · obtain ⟨x, hx⟩ := ‹_›
      have := moves_toGameForm Player.right g
      simp_all [Set.ext_iff]
  · apply GameForm.ext
    intro p
    simp only [Shove.toGameForm, GameGraph.moves_toForm, Form.moves_zero, Set.image_eq_empty]
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    obtain ⟨n, hn, rfl⟩ := (Shove.mem_moves_iff p g x).mp hx
    simp_all only [Piece.none_ne_ofPlayer]

theorem toGameForm_push_mem_moves (s : Shove) (p : Player) {m : ℕ}
    (hm : s.board m = .ofPlayer p) :
    (s.push_on m).toGameForm ∈ Form.moves p s.toGameForm := by
  rw [moves_toGameForm]
  refine ⟨s.push_on m, ?_, rfl⟩
  rw [mem_moves_iff p s _]
  use m

theorem mem_moves_toGameForm_iff (s : Shove) (p : Player) (g' : GameForm) :
    g' ∈ Form.moves p s.toGameForm ↔
    ∃ m, s.board m = .ofPlayer p ∧ g' = (s.push_on m).toGameForm := by
  rw [moves_toGameForm]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨s', hs', rfl⟩
    obtain ⟨m, hm, rfl⟩ := (mem_moves_iff p s s').mp hs'
    use m
  · rintro ⟨m, hm, rfl⟩
    use s.push_on m
    refine ⟨?_, rfl⟩
    rw [mem_moves_iff]
    use m

/-! ### Properties of rightmostPos -/

noncomputable def rightmostPos (s : Shove) : ℕ :=
  Nat.findGreatest (fun n => s.board n ≠ .none) s.finite_support.choose

theorem rightmostPos_le (s : Shove) : s.rightmostPos ≤ s.finite_support.choose :=
  Nat.findGreatest_le _

theorem rightmostPos_spec (s : Shove) {k : ℕ} (hk : k ≤ s.finite_support.choose)
    (hne : s.board k ≠ .none) : s.board s.rightmostPos ≠ .none := by
  unfold rightmostPos
  exact Nat.findGreatest_spec (P := fun n => s.board n ≠ .none) hk hne

theorem board_eq_none_of_gt_rightmostPos (s : Shove) {k : ℕ}
    (hk : s.rightmostPos < k) :
    s.board k = .none := by
  unfold rightmostPos at hk
  by_cases hk2 : k ≤ s.finite_support.choose
  · by_contra h
    exact absurd (Nat.le_findGreatest hk2 h) (not_le.mpr hk)
  · simp at hk2
    grind only [Exists.choose_spec]

theorem rightmostPos_greatest (s : Shove) {k : ℕ} (hk : s.board k ≠ .none) :
    k ≤ s.rightmostPos := by
  by_contra h
  push_neg at h
  have hk2 : k ≤ s.finite_support.choose := by
    by_contra h2; push_neg at h2
    exact hk (s.finite_support.choose_spec k (by omega))
  exact hk (board_eq_none_of_gt_rightmostPos s h)

theorem board_eq_none_of_rightmostPos_zero (s : Shove)
    (h0 : s.rightmostPos = 0) (hb : s.board 0 = .none) : ∀ n, s.board n = .none := by
  intro n
  by_contra h
  have h1 := rightmostPos_greatest s h
  rw [h0] at h1
  interval_cases n
  exact h hb

/-! ### Stride definition and properties under push_on -/

protected noncomputable def stride (s : Shove) (p : Player) : ℕ :=
  if s.board s.rightmostPos = .ofPlayer p then s.rightmostPos + 1
  else 0

theorem rightmostPos_push_below (s : Shove) {m : ℕ}
    (hm : m < s.rightmostPos) :
    (s.push_on m).rightmostPos = s.rightmostPos := by
  apply Nat.le_antisymm _ _;
  · apply Nat.le_of_not_gt; intro h_contra; (
    obtain ⟨j, hj_gt, hj_ne⟩ : ∃ j, j > s.rightmostPos ∧ (s.push_on m).board j ≠ .none := by
      have := Nat.findGreatest_eq_iff.mp (refl (s.push_on m).rightmostPos)
      use (s.push_on m).rightmostPos, h_contra
      exact this.2.1 (by omega)
    have h_push_on_eq : (s.push_on m).board j = s.board j := Shove.push_on_gt _ (by omega)
    rw [h_push_on_eq] at hj_ne
    exact absurd (rightmostPos_greatest s hj_ne) hj_gt.not_ge)
  · refine' rightmostPos_greatest _ _;
    rw [ Shove.push_on_gt ];
    · have : Nat.findGreatest (fun n => s.board n ≠ Piece.none) s.finite_support.choose = s.rightmostPos := rfl
      have := Nat.findGreatest_eq_iff.mp this
      lia
    · assumption

theorem rightmostPos_push_at (s : Shove) {k : ℕ}
    (hk : s.rightmostPos = k) (hpos : 0 < k) (hne : s.board k ≠ .none) :
    (s.push_on k).rightmostPos = k - 1 := by
  apply le_antisymm
  · by_contra h_gt; push_neg at h_gt
    have h_push_none : ∀ j, j ≥ k → (s.push_on k).board j = .none := by
      intro j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | h_gt_k
      · exact push_on_eq s k
      · rw [push_on_gt s h_gt_k]
        by_contra h_ne'
        exact absurd (rightmostPos_greatest s h_ne') (by omega)
    have h_witness : (s.push_on k).board (k - 1) ≠ .none := by
      rcases k with (_ | k) <;> simp_all +decide [Shove.push_on]
    have h_k_le : k - 1 ≤ (s.push_on k).finite_support.choose := by
      by_contra h_lt; push_neg at h_lt
      exact h_witness ((s.push_on k).finite_support.choose_spec (k - 1) (by omega))
    have h_ne := rightmostPos_spec (s.push_on k) h_k_le h_witness
    exact h_ne (h_push_none _ (by omega))
  · apply rightmostPos_greatest
    rcases k with (_ | k) <;> simp_all +decide [Shove.push_on]

theorem stride_push_below (s : Shove) (p : Player) {m : ℕ}
    (hm : m < s.rightmostPos) :
    (s.push_on m).stride p = s.stride p := by
  unfold Shove.stride;
  rw [rightmostPos_push_below s hm, Shove.push_on]
  grind only

theorem stride_push_at_rightmost (s : Shove) (p : Player) {k : ℕ}
    (hk : s.rightmostPos = k) (hpos : 0 < k)
    (hp : s.board k = .ofPlayer p) :
    (s.push_on k).stride p = k := by
  have h_push : (s.push_on k).rightmostPos = k - 1 := by
    exact rightmostPos_push_at s hk hpos ( by cases p <;> aesop );
  rcases k with ( _ | k ) <;> simp_all +decide [ Shove.stride ]

theorem stride_neg_push_at_rightmost (s : Shove) (p : Player) {k : ℕ}
    (hk : s.rightmostPos = k)
    (hp : s.board k = .ofPlayer p) (hpos : 0 < k) :
    (s.push_on k).stride (-p) = 0 := by
  have h_rightmostPos : (s.push_on k).rightmostPos = k - 1 := by
    convert rightmostPos_push_at s hk hpos ( hp.symm ▸ by cases p <;> trivial ) using 1;
  have h_board : (s.push_on k).board (k - 1) = Piece.ofPlayer p := by
    rcases k with ( _ | k ) <;> simp_all +decide [ Shove.push_on ];
  simp_all [Shove.stride];
  cases p <;> tauto

theorem stride_neg_eq_zero (s : Shove) (p : Player)
    (hp : s.board s.rightmostPos = .ofPlayer p) :
    s.stride (-p) = 0 := by
  cases p <;> simp_all +decide [Shove.stride]

theorem push_rightmost_zero_empty (s : Shove)
    (h0 : s.rightmostPos = 0) (n : ℕ) :
    (s.push_on 0).board n = .none := by
  simp only [push_on, not_lt_zero, ↓reduceIte, ite_eq_left_iff]
  intro hn
  simp only [rightmostPos, ne_eq, Nat.findGreatest_eq_zero_iff, not_not] at h0
  by_cases h_sup : n ≤ s.finite_support.choose
  · exact h0 (Nat.ne_zero_iff_zero_lt.mp hn) h_sup
  · rw [not_le] at h_sup
    exact Exists.choose_spec s.finite_support n (Nat.le_of_succ_le h_sup)

theorem stride_neg_zero_of_p_move (s : Shove) (p : Player) {m : ℕ}
    (hrm : s.board s.rightmostPos = .ofPlayer p)
    (hm : s.board m = .ofPlayer p) :
    (s.push_on m).stride (-p) = 0 := by
  by_cases hm' : m < s.rightmostPos;
  · convert stride_neg_eq_zero ( s.push_on m ) p _ using 1;
    rw [rightmostPos_push_below] <;> aesop;
  · have hm'' : m = s.rightmostPos := by
      exact le_antisymm (rightmostPos_greatest s (by aesop)) (not_lt.mp hm')
    by_cases h : 0 < s.rightmostPos <;> simp_all +decide [ Shove.stride ]
    · convert stride_neg_push_at_rightmost s p rfl hrm h using 1;
      unfold Shove.stride; aesop
    · rw [push_rightmost_zero_empty s h (s.push_on 0).rightmostPos]
      exact Piece.none_ne_ofPlayer (-p)

theorem stride_push_eq_rightmostPos (s : Shove) (p : Player) {m : ℕ}
    (hm1 : s.board m ≠ .none) (hm2 : m = s.rightmostPos) :
    (s.push_on m).stride p = s.stride p - 1 := by
  subst hm2
  by_cases h1 : 0 < s.rightmostPos
  · have h2 := rightmostPos_push_at s rfl h1 hm1
    have h3 := push_on_lt s (Nat.sub_one_lt_of_lt h1)
    have h4 : s.rightmostPos - 1 + 1 = s.rightmostPos := Nat.sub_add_cancel h1
    simp only [Shove.stride, h2, h3, h4]
    split_ifs <;> omega
  · simp only [not_lt, nonpos_iff_eq_zero, ne_eq] at h1 hm1
    rw [h1] at ⊢ hm1
    simp only [Shove.stride, h1, zero_add]
    split_ifs with h2 h3
    · absurd push_rightmost_zero_empty s h1 (s.push_on 0).rightmostPos
      exact Piece.ne_none_of_ofPlayer h2
    · absurd h2
      rw [push_rightmost_zero_empty s h1 (s.push_on 0).rightmostPos]
      exact Piece.none_ne_ofPlayer p
    · rfl
    · rfl

theorem stride_push_le (s : Shove) (p : Player) {m : ℕ}
    (hm : s.board m ≠ .none) :
    (s.push_on m).stride p ≤ s.stride p := by
  obtain h_lt | h_eq | h_gt := Nat.lt_trichotomy m s.rightmostPos
  · exact Nat.le_of_eq (stride_push_below s p h_lt)
  · rw [stride_push_eq_rightmostPos s p hm h_eq]
    exact Nat.sub_le (s.stride p) 1
  · absurd h_gt
    rw [not_lt]
    exact rightmostPos_greatest s hm

theorem stride_zero_of_push (g : Shove) (p : Player) {m : ℕ}
    (hs : g.stride p = 0) (hm : g.board m ≠ .none) :
    (g.push_on m).stride p = 0 := by
  have := stride_push_le g p hm
  omega

theorem push_to_empty_is_neg (g : Shove) (p : Player) {m : ℕ}
    (hs : g.stride p = 0)
    (hm_piece : g.board m ≠ .none)
    (h_empty : ∀ n, (g.push_on m).board n = .none) :
    g.board m = .ofPlayer (-p) := by
  have h_m_eq_rightmostPos : m = g.rightmostPos := by
    refine' le_antisymm ( Shove.rightmostPos_greatest _ hm_piece ) _;
    contrapose! h_empty
    use g.rightmostPos
    have := Shove.rightmostPos_le g
    convert rightmostPos_spec g (by omega) hm_piece using 1
    exact push_on_gt g h_empty
  cases p <;> cases h : g.board m <;> simp_all +decide [ Shove.stride ]

theorem isSolved_of_stride_zero {p : Player} (g : Shove)
    (hs : g.stride p = 0) :
    GameForm.IsSolved p g.toGameForm := by
  induction' n' : g.weight using Nat.strong_induction_on with n ih generalizing g;
  by_cases h_empty : ∀ n, g.board n = .none;
  · rw [ Shove.toGameForm_zero_iff g |>.2 h_empty ] ; exact GameForm.isSolved_zero p;
  · obtain ⟨k, hk⟩ : ∃ k, g.board k = .ofPlayer (-p) ∧ k = g.rightmostPos := by
      have h_rightmost : g.board g.rightmostPos ≠ .none := by
        obtain ⟨n, hn⟩ : ∃ n, g.board n ≠ .none := by
          exact not_forall.mp h_empty;
        exact g.rightmostPos_spec ( show n ≤ g.finite_support.choose from le_of_not_gt fun h => hn <| g.finite_support.choose_spec n h.le ) hn
      generalize_proofs at *; (
      cases h : g.board g.rightmostPos <;> simp_all +decide [ Shove.stride ];
      · cases p <;> tauto;
      · cases p <;> tauto);
    rw [GameForm.isSolved_def]
    refine ⟨?_, ?_, ?_⟩
    · intro h₁
      obtain ⟨ m, hm₁, hm₂ ⟩ := ( Shove.mem_moves_toGameForm_iff g p 0 ).mp h₁;
      have h_piece_neg : g.board m = .ofPlayer (-p) := by
        apply Shove.push_to_empty_is_neg g p hs (by
        exact hm₁.symm ▸ by cases p <;> tauto;) (by
        exact fun n => by simpa using Shove.toGameForm_zero_iff ( g.push_on m ) |>.1 hm₂.symm n;);
      cases p <;> cases h : g.board m <;> simp_all +decide;
    · intro h_nonzero
      have h_move : (g.push_on k).toGameForm ∈ Form.moves (-p) g.toGameForm := by
        exact Shove.toGameForm_push_mem_moves g ( -p ) hk.1;
      exact Form.not_isEnd_of_mem_moves h_move
    · intro gp hgp
      obtain ⟨q, m, hm⟩ : ∃ q m, gp = (g.push_on m).toGameForm ∧ g.board m = .ofPlayer q := by
        obtain ⟨ q, hq ⟩ := hgp;
        obtain ⟨ ⟨ q, rfl ⟩, hq ⟩ := hq;
        exact Exists.elim ( Shove.mem_moves_toGameForm_iff g q gp |>.1 hq ) fun m hm => ⟨ q, m, hm.2, hm.1 ⟩;
      grind only [Piece.ofPlayer_ne_none, stride_zero_of_push, weight_push_lt]

theorem rightmost_of_stride_pos {p : Player} {g : Shove}
    (hs : g.stride p ≠ 0) :
    g.board g.rightmostPos = .ofPlayer p ∧ g.rightmostPos + 1 = g.stride p := by
  unfold Shove.stride at *; aesop;

theorem neg_push_below_rightmost (g : Shove) (p : Player) {m : ℕ}
    (hrm : g.board g.rightmostPos = .ofPlayer p)
    (hm : g.board m = .ofPlayer (-p)) :
    m < g.rightmostPos := by
  refine' lt_of_le_of_ne ( _ : m ≤ g.rightmostPos ) _;
  · exact Shove.rightmostPos_greatest _ ( by aesop );
  · rintro rfl; cases p <;> cases hm.symm.trans hrm

set_option maxHeartbeats 1600000 in
/--
Every `Shove` board has stride
-/
theorem toGameForm_hasStride (g : Shove) (p : Player) :
    GameForm.HasStride p g.toGameForm (g.stride p) := by
  induction w : g.weight using Nat.strong_induction_on generalizing g p with
  | _ w ih =>
  -- Helper: IH gives HasStride for any push
  have ih_push : ∀ (m : ℕ) (q : Player), g.board m ≠ .none →
      GameForm.HasStride q (g.push_on m).toGameForm ((g.push_on m).stride q) := by
    intro m q hm
    exact ih _ (by rw [← w]; exact weight_push_lt g m hm) (g.push_on m) q rfl
  by_cases hs : g.stride p = 0
  · rw [hs]; exact GameForm.hasStride_zero_iff.mpr (isSolved_of_stride_zero g hs)
  · obtain ⟨hrm, hrm_eq⟩ := rightmost_of_stride_pos hs
    set k := g.rightmostPos with hk_def
    have hstride_eq : g.stride p = k + 1 := by omega
    rw [hstride_eq]
    have hk_ne : g.board k ≠ .none := by rw [hrm]; exact Piece.ofPlayer_ne_none p
    rw [GameForm.hasStride_succ_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro H
      have h_push_k_mem : (g.push_on k).toGameForm ∈ Form.moves p g.toGameForm :=
        toGameForm_push_mem_moves g p hrm
      have h_push_k_opt : Form.IsOption (g.push_on k).toGameForm g.toGameForm :=
        Form.IsOption.of_mem_moves h_push_k_mem
      have h_push_k_solved := GameForm.isSolved_of_isOption H h_push_k_opt
      by_cases hk_pos : 0 < k
      · have h_stride_k : (g.push_on k).stride p = k := stride_push_at_rightmost g p rfl hk_pos hrm
        have h_hs_k := ih_push k p hk_ne
        rw [h_stride_k] at h_hs_k
        have := (GameForm.hasStride_isSolved_iff_zero h_hs_k).mp h_push_k_solved
        omega
      · have hk_zero : (k : ℕ) = 0 := by omega
        have h_empty : ∀ n, (g.push_on 0).board n = .none :=
          push_rightmost_zero_empty g (by rw [← hk_def]; exact hk_zero)
        have h_zero : (g.push_on k).toGameForm = 0 := by
          rw [hk_zero]; exact (toGameForm_zero_iff _).mpr (fun n => h_empty n)
        rw [h_zero] at h_push_k_mem
        exact GameForm.isSolved_zero_not_mem H h_push_k_mem
    · intro g' hg'
      obtain ⟨m, hm_p, rfl⟩ := (mem_moves_toGameForm_iff g p g').mp hg'
      have hm_ne : g.board m ≠ .none := by rw [hm_p]; exact Piece.ofPlayer_ne_none p
      have h_stride_ge : k ≤ (g.push_on m).stride p := by
        by_cases hm_lt : m < g.rightmostPos
        · rw [stride_push_below g p hm_lt, hstride_eq]
          omega
        · have hm_eq : m = g.rightmostPos := by
            refine le_antisymm ?_ (Nat.not_lt.mp hm_lt)
            apply rightmostPos_greatest g
            rw [hm_p]
            exact Piece.ofPlayer_ne_none p
          have := stride_push_eq_rightmostPos g p hm_ne hm_eq
          omega
      exact ⟨(g.push_on m).stride p, h_stride_ge, ih_push m p hm_ne⟩
    · refine ⟨(g.push_on k).toGameForm, toGameForm_push_mem_moves g p hrm, ?_, ?_⟩
      · by_cases hk_pos : 0 < k
        · have h_str := stride_push_at_rightmost g p rfl hk_pos hrm
          have h_hs := ih_push k p hk_ne
          rwa [h_str] at h_hs
        · have hk_zero : (k : ℕ) = 0 := by omega
          have h_empty : ∀ n, (g.push_on 0).board n = .none :=
            push_rightmost_zero_empty g (by rw [← hk_def]; exact hk_zero)
          have h_zero : (g.push_on k).toGameForm = 0 := by
            rw [hk_zero]; exact (toGameForm_zero_iff _).mpr (fun n => h_empty n)
          rw [h_zero, hk_zero]
          exact GameForm.hasStride_zero_iff.mpr (GameForm.isSolved_zero p)
      · intro g'' hg'' m_val hm_val
        obtain ⟨m', hm'_p, rfl⟩ := (mem_moves_toGameForm_iff g p g'').mp hg''
        have hm'_ne : g.board m' ≠ .none := by rw [hm'_p]; exact Piece.ofPlayer_ne_none p
        have h_neg_stride : (g.push_on m').stride (-p) = 0 :=
          stride_neg_zero_of_p_move g p hrm hm'_p
        have h_m_zero : m_val = 0 := by
          have := ih_push m' (-p) hm'_ne
          rw [h_neg_stride] at this
          exact GameForm.hasStride_unique hm_val this
        rw [h_m_zero] at hm_val ⊢; clear h_m_zero
        have h_neg_good : (g.push_on k).stride (-p) = 0 :=
          stride_neg_zero_of_p_move g p hrm hrm
        exact ⟨0, le_refl _, by rw [← h_neg_good]; exact ih_push k (-p) hk_ne⟩
    · intro g' hg'
      obtain ⟨m, hm_neg, rfl⟩ := (mem_moves_toGameForm_iff g (-p) g').mp hg'
      have hm_lt : m < k := neg_push_below_rightmost g p hrm hm_neg
      have hm_ne : g.board m ≠ .none := by rw [hm_neg]; exact Piece.ofPlayer_ne_none (-p)
      have h_stride_eq : (g.push_on m).stride p = k + 1 := by
        rw [stride_push_below g p (by rw [← hk_def]; exact hm_lt), hstride_eq]
      use k + 1
      refine ⟨le_refl _, ?_⟩
      rw [← h_stride_eq]
      exact ih_push m p hm_ne
    · intro hne
      have ⟨g', hg'⟩ := Set.nonempty_iff_ne_empty.mpr hne
      obtain ⟨m, hm_neg, rfl⟩ := (mem_moves_toGameForm_iff g (-p) g').mp hg'
      have hm_lt : m < k := neg_push_below_rightmost g p hrm hm_neg
      have hm_ne : g.board m ≠ .none := by rw [hm_neg]; exact Piece.ofPlayer_ne_none (-p)
      have h_stride_eq : (g.push_on m).stride p = k + 1 := by
        rw [stride_push_below g p (by rw [← hk_def]; exact hm_lt), hstride_eq]
      use (g.push_on m).toGameForm
      use (mem_moves_toGameForm_iff g (-p) _).mpr ⟨m, hm_neg, rfl⟩
      rw [← h_stride_eq]
      exact ih_push m p hm_ne

protected def zero : Shove := { board := fun _ => .none, finite_support := by use 0; intro _ _; rfl }

@[simp]
protected def zero_toGameForm : Shove.zero.toGameForm = 0 := by
  ext p x
  simp only [moves_toGameForm, Shove.moves, Piece.none_ne_ofPlayer, Set.setOf_false,
             Set.image_empty, Set.mem_empty_iff_false, Form.moves_zero, Shove.zero]

noncomputable instance : Ruleset Shove where
  toGameForm := Shove.toGameForm
  moves_toGameForm p r g' h_g' := by
    simp only [moves_toGameForm, Set.mem_image] at h_g'
    obtain ⟨r', _, h_r'⟩ := h_g'
    use r'

private def mk_with_stride (p : Player) (n : ℕ) :
    ∃ g, Ruleset.Forms Shove g ∧ HasStride p g n ∧ HasStride (-p) g 0 := by
    match n with
    | 0 =>
      use 0
      constructor
      · rw [<-Shove.zero_toGameForm]
        exact Ruleset.Forms.position_mem Shove.zero
      · simp only [GameForm.hasStride_zero_iff, GameForm.isSolved_zero, and_self]
    | n + 1 =>
      let s: Shove :=
        { board k := if n == k then Piece.ofPlayer p else .none
        , finite_support := by
            use (n + 1)
            intro x h_x
            split_ifs with h
            · rw [beq_iff_eq] at h
              omega
            · rfl
        }
      use s.toGameForm
      have h_n_rightmost : s.rightmostPos = n := by
        subst s
        simp only [rightmostPos, beq_iff_eq, ne_eq, ite_eq_right_iff, Piece.ofPlayer_ne_none,
                   imp_false, Decidable.not_not, Nat.findGreatest_eq_iff, implies_true, true_and]
        grind only [Exists.choose_spec]
      have : s.board s.rightmostPos = Piece.ofPlayer p := by
        subst s
        grind only
      refine ⟨?_, ?_, ?_⟩
      · exact Ruleset.Forms.position_mem s
      · convert toGameForm_hasStride s p
        subst s
        simp only [Shove.stride, beq_iff_eq, ite_eq_left_iff, Piece.none_ne_ofPlayer, imp_false]
        split_ifs with h <;> grind only
      · convert toGameForm_hasStride s (-p)
        subst s
        simp only [Shove.stride, beq_iff_eq, right_eq_ite_iff, and_false, imp_false,
                   Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero]
        split_ifs with h
        · simp [Piece.ofPlayer]
          cases p <;> simp only [reduceCtorEq, not_false_eq_true]
        · exact Piece.none_ne_ofPlayer (-p)

instance : GameForm.Strided (AdditiveClosure (Ruleset.Forms Shove)) where
  mk_with_strides l r := AdditiveClosure.mk_with_strides_aux Shove.mk_with_stride l r
  has_stride p := AdditiveClosure.has_stride_aux p Shove.stride Shove.toGameForm_hasStride

protected noncomputable def equivInt : MisereQuotient (AdditiveClosure (Ruleset.Forms Shove)) ≃ ℤ :=
  GameForm.MisereQuotient.stridedEquivInt

protected theorem le_iff_equiv_ge (a b : MisereQuotient (AdditiveClosure (Ruleset.Forms Shove))) :
    a ≤ b ↔
    GameForm.MisereQuotient.stridedEquivInt a ≥ GameForm.MisereQuotient.stridedEquivInt b :=
    GameForm.MisereQuotient.le_iff_equiv_ge a b

end Shove
