/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.GameForm
public import CombinatorialGames.Form.Misere.Outcome

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
    ∧ (∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n)
    ∧ (∀ g' ∈ moves (-p) g, HasStride p g' (n + 1))
termination_by birthday g
decreasing_by all_goals exact birthday_lt_of_mem_moves (by assumption)

/--
Stride equals zero if game is solved
-/
@[simp]
theorem hasStride_zero_iff {p : Player} {g : GameForm} :
    HasStride p g 0 ↔ IsSolved p g := by
  constructor
  · intro h_hasStride
    unfold HasStride at h_hasStride
    exact h_hasStride
  · intro h_isSolved
    unfold HasStride
    exact h_isSolved

/--
Game is solved if its stride equals zero
-/
theorem hasStride_isSolved_iff_zero {p : Player} {g : GameForm} {n : ℕ} (h_hasStride : HasStride p g n) :
    IsSolved p g ↔ n = 0 := by
  unfold HasStride at h_hasStride
  constructor
  · intro h_isSolved
    match n with
    | .zero => rfl
    | .succ k =>
      dsimp only at h_hasStride
      exfalso
      exact h_hasStride.left h_isSolved
  · intro h_zero
    subst h_zero
    exact h_hasStride

theorem hasStride_succ_iff {p : Player} {g : GameForm} {n : ℕ} :
    HasStride p g (n + 1) ↔
    ¬IsSolved p g
    ∧ (∀ g' ∈ moves p g, ∃ k, n ≤ k ∧ HasStride p g' k)
    ∧ (∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n)
    ∧ (∀ g' ∈ moves (-p) g, HasStride p g' (n + 1)) := by
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
    ∃ g', ∃ (_ : g' ∈ moves p g), HasStride p g' n :=
  (hasStride_succ_iff.mp h).2.2.1

/--
If the stride of $G$ is not zero then every opponent move preserves the stride
-/
theorem hasStride_succ_support_neg {p : Player} {g : GameForm} {n : ℕ}
    (h : HasStride p g (n + 1)) (g' : GameForm) (hg' : g' ∈ moves (-p) g) :
    HasStride p g' (n + 1) :=
  (hasStride_succ_iff.mp h).2.2.2 g' hg'

theorem hasStride_succ_not_isEnd {p : Player} {g : GameForm} {n : ℕ}
    (h : HasStride p g (n + 1)) : ¬IsEnd p g := by
  have ⟨_, h_mem, _⟩ := hasStride_succ_exists_best h
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
    have ⟨g1, hg1_mem, hg1_stride⟩ := hasStride_succ_exists_best h_n
    have ⟨j, hkj, hj_stride⟩ := hasStride_succ_support h_k g1 hg1_mem
    have h_nj : n = j := hasStride_unique hg1_stride hj_stride
    subst h_nj
    have ⟨g2, hg2_mem, hg2_stride⟩ := hasStride_succ_exists_best h_k
    have ⟨j', hnj', hj'_stride⟩ := hasStride_succ_support h_n g2 hg2_mem
    have h_kj' : k = j' := hasStride_unique hg2_stride hj'_stride
    subst h_kj'
    exact Nat.le_antisymm hnj' hkj
termination_by birthday g
decreasing_by all_goals exact birthday_lt_of_mem_moves (by assumption)

theorem hasStride_of_mem_moves {p : Player} {g g' : GameForm} {n : ℕ}
    (hg : HasStride p g n) (hm : g' ∈ moves p g) :
    ∃ j, n - 1 ≤ j ∧ HasStride p g' j := by
  match n with
  | 0 => exact ⟨0, Nat.zero_le _, hasStride_zero_iff.mpr (isSolved_of_mem_moves (hasStride_zero_iff.mp hg) hm)⟩
  | .succ n =>
    have ⟨j, hj, hjs⟩ := hasStride_succ_support hg g' hm
    exact ⟨j, by simpa only [Nat.succ_eq_add_one, add_tsub_cancel_right] using hj, hjs⟩

theorem hasStride_of_mem_moves_neg {p : Player} {g g' : GameForm} {n : ℕ}
    (hg : HasStride p g n) (hm : g' ∈ moves (-p) g) : HasStride p g' n := by
  match n with
  | 0 => exact hasStride_zero_iff.mpr (isSolved_of_mem_moves (hasStride_zero_iff.mp hg) hm)
  | .succ n => exact hasStride_succ_support_neg hg g' hm

/--
Stride of sum is the sum of strides
-/
theorem hasStride_add {p : Player} {g h : GameForm} {n k : ℕ}
    (h_g : HasStride p g n) (h_h : HasStride p h k) :
    HasStride p (g + h) (n + k) := by
  obtain h_zero | h_pos := Nat.eq_zero_or_pos (n + k)
  · -- If both n = 0 and k = 0 then G + H is solved and thus has stride of zero
    have hn : n = 0 := Nat.eq_zero_of_add_eq_zero_right h_zero; subst hn
    have hk : k = 0 := Nat.eq_zero_of_add_eq_zero_left h_zero; subst hk
    rw [hasStride_zero_iff]
    exact isSolved_add (hasStride_zero_iff.mp h_g) (hasStride_zero_iff.mp h_h)
  · -- Otherwise n + k > 0
    have ⟨m, hm⟩ : ∃ m, n + k = m + 1 := ⟨n + k - 1, by omega⟩
    rw [hm]
    apply hasStride_succ_iff.mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- At least one of n, k is non-zero so either G or H is not solved so G + H is not solved
      obtain hn | hn := Nat.eq_zero_or_pos n
      · exact not_isSolved_add_right ((hasStride_isSolved_iff_zero h_h).not.mpr (by omega))
      · exact not_isSolved_add_left ((hasStride_isSolved_iff_zero h_g).not.mpr (Nat.ne_zero_iff_zero_lt.mpr hn))
    · intro gh' hgh'
      simp only [moves_add, Set.mem_union, Set.mem_image] at hgh'
      obtain ⟨g', hg', rfl⟩ | ⟨h', hh', rfl⟩ := hgh'
      · have ⟨j_g, hj_g, hj_gs⟩ := hasStride_of_mem_moves h_g hg'
        exact ⟨j_g + k, by omega, hasStride_add hj_gs h_h⟩
      · have ⟨j_h, hj_h, hj_hs⟩ := hasStride_of_mem_moves h_h hh'
        exact ⟨n + j_h, by omega, hasStride_add h_g hj_hs⟩
    · obtain hn | hn := Nat.eq_zero_or_pos n
      · subst hn
        have ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        subst hk'
        have ⟨h1, hh1_mem, hh1_s⟩ := hasStride_succ_exists_best h_h
        refine ⟨g + h1, add_left_mem_moves_add hh1_mem g, ?_⟩
        have := hasStride_add h_g hh1_s
        convert this using 1; omega
      · have ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, (Nat.sub_eq_iff_eq_add hn).mp rfl⟩
        subst hn'
        have ⟨g1, hg1_mem, hg1_s⟩ := hasStride_succ_exists_best h_g
        refine ⟨g1 + h, add_right_mem_moves_add hg1_mem h, ?_⟩
        have := hasStride_add hg1_s h_h
        convert this using 1; omega
    · intro gh' hgh'
      simp only [moves_add, Set.mem_union, Set.mem_image] at hgh'
      obtain ⟨g', hg', rfl⟩ | ⟨h', hh', rfl⟩ := hgh'
      · have hg'_s := hasStride_of_mem_moves_neg h_g hg'
        have := hasStride_add hg'_s h_h
        rwa [hm] at this
      · have hh'_s := hasStride_of_mem_moves_neg h_h hh'
        have := hasStride_add h_g hh'_s
        rwa [hm] at this
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
    have ⟨g1, hg1_mem, hg1_stride_p⟩ := hasStride_succ_exists_best h_l
    have hg1_stride_neg : HasStride (-p) g1 (r' + 1) := by
      have : g1 ∈ moves (- -p) g := by rw [neg_neg]; exact hg1_mem
      exact hasStride_succ_support_neg h_r g1 this
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
        have hg1_solved := hasStride_zero_iff.mp hg1_stride_p
        exact isSolved_winsGoingFirst (isSolved_of_isOption hg1_solved (IsOption.of_mem_moves hg2_mem))
      | .succ l'' =>
        have hg2_stride_p : HasStride p g2 (l'' + 1) := hasStride_succ_support_neg hg1_stride_p g2 hg2_mem
        have ⟨k, hk_ge, hg2_stride_neg⟩ := hasStride_succ_support hg1_stride_neg g2 hg2_mem
        have h_le' : l'' + 1 ≤ k := by omega
        exact hasStride_winsGoingFirst hg2_stride_p hg2_stride_neg h_le'
termination_by g
decreasing_by form_wf

private theorem hasStride_not_winsGoingFirst {p : Player} {g : GameForm} {l r : ℕ}
    (h_l : HasStride p g l) (h_r : HasStride (-p) g r) (h_gt : r < l) :
    ¬WinsGoingFirst p g := by
  rw [not_winsGoingFirst_iff]
  constructor
  · rw [isEndLike_iff_isEnd]
    have ⟨l', hl'⟩ : ∃ l', l = l' + 1 := ⟨l - 1, (Nat.sub_eq_iff_eq_add (Nat.one_le_of_lt h_gt)).mp rfl⟩
    subst hl'
    exact hasStride_succ_not_isEnd h_l
  · intro g' hg'
    obtain ⟨k, hk_ge, hk_stride⟩ := hasStride_of_mem_moves h_l hg'
    have h_neg_stride : HasStride (-p) g' r := by
      match r with
      | 0 => exact hasStride_zero_iff.mpr (isSolved_of_mem_moves (hasStride_zero_iff.mp h_r) hg')
      | .succ r' => exact hasStride_succ_support_neg h_r g' (by rwa [neg_neg])
    have h_rk : r ≤ k := by omega
    exact hasStride_winsGoingFirst h_neg_stride (by rwa [neg_neg]) h_rk

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
theorem hasStride_misereOutcome_iff {p : Player} {g : GameForm} {l r : ℕ}
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
