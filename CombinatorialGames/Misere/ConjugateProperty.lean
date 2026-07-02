/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.SimplestForm
public import CombinatorialGames.Misere.Expansion
public import Mathlib.Algebra.BigOperators.Intervals

universe u

public section

namespace AugmentedForm

open Form
open Form.Misere.Outcome

variable {A : AugmentedForm.{u} → Prop}

/--
A finite sum of elements of an additively-closed universe stays in the universe
 -/
theorem mem_sum [ShortUniverse A] {ι : Type*} (s : Finset ι) (f : ι → AugmentedForm)
    (hf : ∀ i ∈ s, A (f i)) : A (∑ i ∈ s, f i) := by
  classical
  revert hf
  induction s using Finset.induction with
  | empty => intro _; simpa using ‹ShortUniverse A›.zero_mem
  | @insert a s ha ih =>
      intro hf
      rw [Finset.sum_insert ha]
      exact ‹ShortUniverse A›.has_add _ _ (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/--
A finite sum of games that are each $\le_{\mathcal{A}} 0$ is itself $\le_{\mathcal{A}} 0$.
-/
theorem sum_misereLE_zero [ShortUniverse A] {ι : Type*} (s : Finset ι)
    (f : ι → AugmentedForm) (h_fi : ∀ i ∈ s, A (f i))
    (h_le : ∀ i ∈ s, (0 : AugmentedForm) ≥m A (f i)) :
    (0 : AugmentedForm) ≥m A (∑ i ∈ s, f i) := by
  classical
  revert h_fi h_le
  induction s using Finset.induction with
  | empty => intro _ _; simp
  | @insert a s ha ih =>
      intro hf hle
      rw [Finset.sum_insert ha]
      have hAS' : A (∑ i ∈ s, f i) :=
        mem_sum s f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hS' : (0 : AugmentedForm) ≥m A (∑ i ∈ s, f i) :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hle i (Finset.mem_insert_of_mem hi))
      have step : (∑ i ∈ s, f i) ≥m A (f a + ∑ i ∈ s, f i) := by
        simpa using misereGE_add_right (A := A) hAS' (hle a (Finset.mem_insert_self a s))
      exact MisereGE.trans hS' step

/--
A finite sum of games that are each $\ge_{\mathcal{A}} 0$ is itself $\ge_{\mathcal{A}} 0$.
-/
theorem sum_misereGE_zero [ShortUniverse A] {ι : Type*} (s : Finset ι)
    (f : ι → AugmentedForm) (h_fi : ∀ i ∈ s, A (f i))
    (h_ge : ∀ i ∈ s, (f i) ≥m A (0 : AugmentedForm)) :
    (∑ i ∈ s, f i) ≥m A (0 : AugmentedForm) := by
  classical
  revert h_fi h_ge
  induction s using Finset.induction with
  | empty => intro _ _; simp
  | @insert a s ha ih =>
      intro hf hge
      rw [Finset.sum_insert ha]
      have hAS' : A (∑ i ∈ s, f i) :=
        mem_sum s f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hS' : (∑ i ∈ s, f i) ≥m A (0 : AugmentedForm) :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hge i (Finset.mem_insert_of_mem hi))
      have step : (f a + ∑ i ∈ s, f i) ≥m A (∑ i ∈ s, f i) := by
        simpa using misereGE_add_right (A := A) hAS' (hge a (Finset.mem_insert_self a s))
      exact MisereGE.trans step hS'

/--
If $t$ is not $\le_{\mathcal{A}} 0$ and $S \ge_{\mathcal{A}} t$, then $S$ is not $\le_{\mathcal{A}} 0$.
-/
theorem not_ge_zero_of_ge {g h : AugmentedForm}
    (h_not_zero_ge_g : ¬ ((0 : AugmentedForm) ≥m A g)) (h_h_ge_g : h ≥m A g) :
    ¬ ((0 : AugmentedForm) ≥m A h) :=
  fun h => h_not_zero_ge_g (MisereGE.trans h h_h_ge_g)

/--
Adding (on the left) a game $r \ge_{\mathcal{A}} 0$ to $t \in \mathcal{A}$ only increases it:
$t + r \ge_{\mathcal{A}} t$.
-/
theorem add_misereGE_self_left [ShortUniverse A] {g h : AugmentedForm}
    (h_g : A g) (h_h_ge_zero : h ≥m A (0 : AugmentedForm)) : (g + h) ≥m A g := by
  have := misereGE_add_right (A := A) h_g h_h_ge_zero
  simpa [add_comm] using this

theorem lemma_3_6_exists_le [ShortUniverse A] {g h : AugmentedForm.{u}}
    (h_g_short : IsShort g) (h_h_short : IsShort h) (h_g : A g)
    (h_g_simplest : SimplestForm A g) (h_gh_eq_zero : (g + h) =m A 0) :
    ∀ g_left ∈ moves .left g, ∃ h_right ∈ moves .right h, ((0 : AugmentedForm) ≥m A (g_left + h_right)) := by
  intro g_left h_g_left_mem
  have h_zero_ge_g_h : (0 : AugmentedForm) ≥m A (g + h) :=
    misereGE_of_misereEQ (MisereEQ.symm h_gh_eq_zero)
  have h_maintenance := (Form.ComparisonSet.maintenance_proviso_of_misereGE
      (U := A) Short.zero (Short.add h_g_short h_h_short) h_zero_ge_g_h).2.1
  have h_mem : g_left + h ∈ moves .left (g + h) :=
    add_right_mem_moves_add h_g_left_mem h
  obtain ⟨option, h_option_mem, h_ge_zero⟩ :=
    (h_maintenance (g_left + h) h_mem).resolve_left (by simp [moves_zero])
  rw [moves_add, Set.mem_union, Set.mem_image, Set.mem_image] at h_option_mem
  rcases h_option_mem with ⟨g_left_right, h_g_left_right_mem, rfl⟩ | ⟨h_right, h_h_right_mem, rfl⟩
  · exfalso
    have h_A_g_left : A g_left := Hereditary.has_option h_g (IsOption.of_mem_moves h_g_left_mem)
    have h_A_g_left_right : A g_left_right :=
      Hereditary.has_option h_A_g_left (IsOption.of_mem_moves h_g_left_right_mem)
    have h_ge : g ≥m A (g_left_right + h + g) := by
      have := misereGE_add_right (A := A) h_g h_ge_zero
      simpa using this
    have h_eq : (g_left_right + h + g) =m A g_left_right := by
      have e : g_left_right + h + g = g_left_right + (g + h) := by rw [add_assoc, add_comm h g]
      rw [e]
      simpa using misereEQ_add_left (A := A) h_A_g_left_right h_gh_eq_zero
    have h_g_ge_g_left_right : g ≥m A g_left_right :=
      misereGE_rw_right (MisereEQ.symm h_eq) h_ge
    exact h_g_simplest.noReversible.1 ⟨g_left, g_left_right, h_g_left_mem, h_g_left_right_mem, h_g_ge_g_left_right⟩
  · exact ⟨h_right, h_h_right_mem, h_ge_zero⟩

theorem lemma_3_6_exists_ge [ShortUniverse A] {g h : AugmentedForm.{u}}
    (h_g_short : IsShort g) (h_h_short : IsShort h) (h_h : A h)
    (h_h_simplest : SimplestForm A h) (h_gh_eq_zero : (g + h) =m A 0) :
    ∀ h_right ∈ moves .right h, ∃ g_left ∈ moves .left g, ((g_left + h_right) ≥m A (0 : AugmentedForm)) := by
  intro h_right h_h_right_mem
  have h_g_h_ge_zero : (g + h) ≥m A (0 : AugmentedForm) :=
    misereGE_of_misereEQ h_gh_eq_zero
  have h_maintenance := (Form.ComparisonSet.maintenance_proviso_of_misereGE
      (U := A) (Short.add h_g_short h_h_short) Short.zero h_g_h_ge_zero).1
  have h_mem : g + h_right ∈ moves .right (g + h) :=
    add_left_mem_moves_add h_h_right_mem g
  obtain ⟨option, h_option_mem, h_ge_zero⟩ :=
    (h_maintenance (g + h_right) h_mem).resolve_left (by simp [moves_zero])
  rw [moves_add, Set.mem_union, Set.mem_image, Set.mem_image] at h_option_mem
  rcases h_option_mem with ⟨g_left, h_g_left_mem, rfl⟩ | ⟨h_right_left, h_h_right_left_mem, rfl⟩
  · exact ⟨g_left, h_g_left_mem, h_ge_zero⟩
  · exfalso
    have h_A_h_right : A h_right :=
      Hereditary.has_option h_h (IsOption.of_mem_moves h_h_right_mem)
    have h_A_h_right_left : A h_right_left :=
      Hereditary.has_option h_A_h_right (IsOption.of_mem_moves h_h_right_left_mem)
    have h_ge : (g + h_right_left + h) ≥m A h := by
      have := misereGE_add_right (A := A) h_h h_ge_zero
      simpa using this
    have h_eq : (g + h_right_left + h) =m A h_right_left := by
      have e : g + h_right_left + h = h_right_left + (g + h) := by rw [add_comm g h_right_left, add_assoc]
      rw [e]
      simpa using misereEQ_add_left (A := A) h_A_h_right_left h_gh_eq_zero
    have h_h_right_left_ge_h : h_right_left ≥m A h :=
      misereGE_rw_left h_eq h_ge
    exact h_h_simplest.noReversible.2 ⟨h_right, h_right_left, h_h_right_mem, h_h_right_left_mem, h_h_right_left_ge_h⟩

theorem sum_Ico_shift_eq {M : Type*} [AddCommMonoid M] (a : ℕ → M) {p q : ℕ}
    (h_pq_le : p ≤ q) (h_a_p_eq_q : a p = a q) :
    (∑ i ∈ Finset.Ico p q, a i) = ∑ i ∈ Finset.Ico p q, a (i + 1) := by
  rcases eq_or_lt_of_le h_pq_le with rfl | h_p_lt_q
  · simp
  · have h_p_mem : p ∈ Finset.Ico p q := Finset.mem_Ico.mpr ⟨le_refl p, h_p_lt_q⟩
    have h_erase : (Finset.Ico p q).erase p = Finset.Ico (p + 1) q :=
      (Nat.Ico_succ_left_eq_erase_Ico).symm
    have h_bot : (∑ i ∈ Finset.Ico p q, a i)
        = a p + ∑ i ∈ Finset.Ico (p + 1) q, a i := by
      rw [← h_erase]
      exact (Finset.add_sum_erase _ a h_p_mem).symm
    have h_rhs : (∑ i ∈ Finset.Ico p q, a (i + 1))
        = (∑ i ∈ Finset.Ico (p + 1) q, a i) + a q := by
      rw [Finset.sum_Ico_add' a p q 1, Finset.sum_Ico_succ_top (Nat.succ_le_of_lt h_p_lt_q) a]
    rw [h_bot, h_rhs, h_a_p_eq_q]
    exact add_comm _ _

theorem lemma_3_6_aeq [ShortUniverse A] {g : AugmentedForm.{u}} (h_g_simplest : SimplestForm A g)
    {x y c : AugmentedForm.{u}}
    (h_x_left_mem : x ∈ moves .left g) (h_y_left_mem : y ∈ moves .left g)
    (h_A_x : A x) (h_A_y : A y)
    (h_zero_ge_x_c : (0 : AugmentedForm) ≥m A (x + c))
    (h_y_c_eq_zero : (y + c) =m A 0) : x = y := by
  have h_y_ge_x : y ≥m A x := by
    have h_x_plus_yc_eq_x : (x + (y + c)) =m A x := by
      convert misereEQ_add_left h_A_x h_y_c_eq_zero using 1
      exact Eq.symm (AddMonoid.add_zero x)
    have h_y_ge_xc_y : y ≥m A ((x + c) + y) := by
      convert misereGE_add_right h_A_y h_zero_ge_x_c using 1
      exact (zero_add y).symm
    have h_comm : x + c + y = x + (y + c) := by
      rw [add_assoc, add_comm c y]
    rw [h_comm] at h_y_ge_xc_y
    exact misereGE_rw_right h_x_plus_yc_eq_x.symm h_y_ge_xc_y
  by_contra h_xy_neq
  exact h_g_simplest.noDominated.1 ⟨x, h_x_left_mem, y, h_y_left_mem, fun h => h_xy_neq h.symm, h_y_ge_x⟩

theorem lemma_3_6_beq [ShortUniverse A] {h_game : AugmentedForm.{u}}
    (h_h_simplest : SimplestForm A h_game)
    {b_n b_n1 a_n1 : AugmentedForm.{u}}
    (h_b_n_right : b_n ∈ moves .right h_game)
    (h_b_n1_right : b_n1 ∈ moves .right h_game)
    (h_A_b_n : A b_n) (h_A_b_n1 : A b_n1)
    (h_a_n1_b_n_ge_zero : (a_n1 + b_n) ≥m A (0 : AugmentedForm))
    (h_a_n1_b_n1_eq_zero : (a_n1 + b_n1) =m A 0) :
    b_n = b_n1 := by
  have h_ge_b_n1 : (a_n1 + b_n + b_n1) ≥m A b_n1 := by
    convert misereGE_add_right h_A_b_n1 h_a_n1_b_n_ge_zero using 1
    exact Eq.symm (AddZeroClass.zero_add b_n1)
  have h_eq_b_n : (a_n1 + b_n + b_n1) =m A b_n := by
    have h_tmp : (b_n + (a_n1 + b_n1)) =m A b_n := by
      convert misereEQ_add_left (hc := h_A_b_n) h_a_n1_b_n1_eq_zero using 1
      exact Eq.symm (AddMonoid.add_zero b_n)
    have h_comm : a_n1 + b_n + b_n1 = b_n + (a_n1 + b_n1) := by
      rw [add_comm a_n1 b_n, add_assoc]
    rw [h_comm]; exact h_tmp
  contrapose! h_h_simplest
  have h_dominated : DominatedRight A h_game b_n := by
    refine ⟨h_b_n_right, b_n1, h_b_n1_right, h_h_simplest.symm, ?_⟩
    exact misereGE_rw_left h_eq_b_n h_ge_b_n1
  exact fun h => h.noDominated.2 ⟨b_n, h_dominated⟩

theorem lemma_3_6_strict [ShortUniverse A] {g h : AugmentedForm.{u}}
    (h_g_simplest : SimplestForm A g) (h_h_simplest : SimplestForm A h)
    (seq_g seq_h : ℕ → AugmentedForm.{u})
    (h_seq_g_left : ∀ n, seq_g n ∈ moves .left g)
    (h_seq_h_right : ∀ n, seq_h n ∈ moves .right h)
    (h_seq_g_A : ∀ n, A (seq_g n)) (h_seq_h_A : ∀ n, A (seq_h n))
    (h_ge_zero_seq : ∀ n, (0 : AugmentedForm) ≥m A (seq_g n + seq_h n))
    (h_next_ge_zero : ∀ n, (seq_g (n + 1) + seq_h n) ≥m A (0 : AugmentedForm))
    (h_bad_start : ¬ ((seq_g 0 + seq_h 0) ≥m A (0 : AugmentedForm))) :
    ∀ n, ¬ ((0 : AugmentedForm) ≥m A (seq_g (n + 1) + seq_h n)) := by
  intro n
  induction n with
  | zero =>
      intro hn
      have heq : (seq_g 1 + seq_h 0) =m A 0 := MisereEq.of_antisymm (h_next_ge_zero 0) hn
      have hceq : seq_g 0 = seq_g 1 :=
        lemma_3_6_aeq h_g_simplest (h_seq_g_left 0) (h_seq_g_left 1) (h_seq_g_A 0) (h_seq_g_A 1)
          (h_ge_zero_seq 0) heq
      have hz : (seq_g 0 + seq_h 0) =m A 0 := by rw [hceq]; exact heq
      exact h_bad_start (misereGE_of_misereEQ hz)
  | succ k IH =>
      intro hn
      have heq : (seq_g (k + 1 + 1) + seq_h (k + 1)) =m A 0 :=
        MisereEq.of_antisymm (h_next_ge_zero (k + 1)) hn
      have hceq : seq_g (k + 1) = seq_g (k + 1 + 1) :=
        lemma_3_6_aeq h_g_simplest (h_seq_g_left (k + 1)) (h_seq_g_left (k + 1 + 1))
          (h_seq_g_A (k + 1)) (h_seq_g_A (k + 1 + 1)) (h_ge_zero_seq (k + 1)) heq
      have heq' : (seq_g (k + 1) + seq_h (k + 1)) =m A 0 := by rw [hceq]; exact heq
      have hbk : seq_h k = seq_h (k + 1) :=
        lemma_3_6_beq h_h_simplest (h_seq_h_right k) (h_seq_h_right (k + 1))
          (h_seq_h_A k) (h_seq_h_A (k + 1)) (h_next_ge_zero k) heq'
      exact IH (by rw [hbk]; exact h_ge_zero_seq (k + 1))

theorem lemma_3_6_descent [ShortUniverse A] {g h : AugmentedForm.{u}}
    (h_g_simplest : SimplestForm A g) (h_h_simplest : SimplestForm A h)
    (seq_g seq_h : ℕ → AugmentedForm.{u})
    (h_seq_g_left : ∀ n, seq_g n ∈ moves .left g)
    (h_seq_h_right : ∀ n, seq_h n ∈ moves .right h)
    (h_seq_g_A : ∀ n, A (seq_g n)) (h_seq_h_A : ∀ n, A (seq_h n))
    (h_finite_left_moves : (moves .left g).Finite)
    (h_ge_zero_seq : ∀ n, (0 : AugmentedForm) ≥m A (seq_g n + seq_h n))
    (h_next_ge_zero : ∀ n, (seq_g (n + 1) + seq_h n) ≥m A (0 : AugmentedForm))
    (h_bad_start : ¬ ((seq_g 0 + seq_h 0) ≥m A (0 : AugmentedForm))) : False := by
  have h_strict := lemma_3_6_strict h_g_simplest h_h_simplest seq_g seq_h
    h_seq_g_left h_seq_h_right h_seq_g_A h_seq_h_A
    h_ge_zero_seq h_next_ge_zero h_bad_start
  obtain ⟨i, j, h_i_lt_j, h_seq_eq⟩ : ∃ i j, i < j ∧ seq_g i = seq_g j := by
    contrapose! h_finite_left_moves
    exact Set.infinite_of_injective_forall_mem
      (fun i j h_ij => le_antisymm (le_of_not_gt fun h_gt => h_finite_left_moves _ _ h_gt h_ij.symm)
        (le_of_not_gt fun h_gt => h_finite_left_moves _ _ h_gt h_ij)) h_seq_g_left
  set p := min i j
  set q := max i j
  have h_p_lt_q : p < q := by
    show min i j < max i j
    omega
  have h_p_eq_i : p = i := by show min i j = i; omega
  have h_q_eq_j : q = j := by show max i j = j; omega
  have h_seq_g_p_eq_q : seq_g p = seq_g q := by
    rw [h_p_eq_i, h_q_eq_j]; exact h_seq_eq
  -- By `h_ge_zero_seq`, S1 ≤ 0. By `h_next_ge_zero`, S2 > 0. So `0 ≥ S2` contradicts `h_strict p`.
  have h_S1_le_zero : (0 : AugmentedForm) ≥m A (∑ k ∈ Finset.Ico p q, (seq_g k + seq_h k)) := by
    exact sum_misereLE_zero _ _ (fun n hn => ClosedUnderAdd.has_add _ _ (h_seq_g_A n) (h_seq_h_A n))
      (fun n hn => h_ge_zero_seq n)
  have h_not_S2_ge_zero : ¬((0 : AugmentedForm) ≥m A (∑ k ∈ Finset.Ico p q, (seq_g (k + 1) + seq_h k))) := by
    apply not_ge_zero_of_ge (h_strict p)
    have h_rest_ge_zero : (∑ k ∈ Finset.Ico p q \ {p}, (seq_g (k + 1) + seq_h k)) ≥m A (0 : AugmentedForm) := by
      apply sum_misereGE_zero
      · exact fun n hn => ClosedUnderAdd.has_add _ _ (h_seq_g_A _) (h_seq_h_A _)
      · exact fun n hn => h_next_ge_zero n
    rw [Finset.sum_eq_add_sum_diff_singleton
      (show p ∈ Finset.Ico p q from Finset.mem_Ico.mpr ⟨le_rfl, h_p_lt_q⟩)]
    apply add_misereGE_self_left
    · exact ClosedUnderAdd.has_add _ _ (h_seq_g_A _) (h_seq_h_A _)
    · exact h_rest_ge_zero
  have h_sum_eq : (∑ k ∈ Finset.Ico p q, (seq_g k + seq_h k))
      = (∑ k ∈ Finset.Ico p q, (seq_g (k + 1) + seq_h k)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        sum_Ico_shift_eq seq_g h_p_lt_q.le h_seq_g_p_eq_q]
  rw [h_sum_eq] at h_S1_le_zero
  exact h_not_S2_ge_zero h_S1_le_zero

/--
This is [Davies, Yadav (Lemma 3.6 on p. 9)][davies:InvertibilityMisereMultiverse:2024]
-/
theorem lemma_3_6 [ShortUniverse A] {g h : AugmentedForm.{u}}
    (h_g_short : IsShort g) (h_h_short : IsShort h) (h_g : A g) (h_h : A h)
    (h_g_simplest : SimplestForm A g) (h_h_simplest : SimplestForm A h)
    (h_gh_eq_zero : (g + h) =m A 0) :
    ∀ g_left ∈ moves .left g, ∃ h_right ∈ moves .right h, (g_left + h_right) =m A 0 := by
  intro g_left h_g_left_mem
  by_contra h_not_exists
  push_neg at h_not_exists
  have h_exists_le := lemma_3_6_exists_le h_g_short h_h_short h_g h_g_simplest h_gh_eq_zero
  have h_exists_ge := lemma_3_6_exists_ge h_g_short h_h_short h_h h_h_simplest h_gh_eq_zero
  have h_sequence : ∀ x ∈ moves .left g, ∃ h_right ∈ moves .right h,
      (0 ≥m A (x + h_right)) ∧ ∃ y ∈ moves .left g, ((y + h_right) ≥m A (0 : AugmentedForm)) := by
    intro x h_x_mem
    obtain ⟨h_right, h_h_right_mem, h_x_h_right_le⟩ := h_exists_le x h_x_mem
    obtain ⟨y, h_y_mem, h_y_h_right_ge⟩ := h_exists_ge h_right h_h_right_mem
    exact ⟨h_right, h_h_right_mem, h_x_h_right_le, y, h_y_mem, h_y_h_right_ge⟩
  choose! h_right_choice h_h_right_mem_choice h_h_right_le_choice
           h_left_next h_h_left_next_mem h_left_next_ge using h_sequence
  set seq_g : ℕ → AugmentedForm := fun n => Nat.rec g_left (fun _ ih => h_left_next ih) n with h_seq_g_def
  have h_seq_g_succ : ∀ n, seq_g (n + 1) = h_left_next (seq_g n) := fun n => rfl
  have h_seq_g_left : ∀ n, seq_g n ∈ moves .left g := by
    intro n
    induction n with
    | zero => exact h_g_left_mem
    | succ n ih => rw [h_seq_g_succ]; exact h_h_left_next_mem (seq_g n) ih
  set seq_h : ℕ → AugmentedForm := fun n => h_right_choice (seq_g n) with h_seq_h_def
  have h_seq_h_right : ∀ n, seq_h n ∈ moves .right h :=
    fun n => h_h_right_mem_choice (seq_g n) (h_seq_g_left n)
  have h_seq_ge_zero : ∀ n, (0 : AugmentedForm) ≥m A (seq_g n + seq_h n) :=
    fun n => h_h_right_le_choice (seq_g n) (h_seq_g_left n)
  have h_seq_next_ge_zero : ∀ n, (seq_g (n + 1) + seq_h n) ≥m A (0 : AugmentedForm) := by
    intro n
    rw [h_seq_g_succ]
    exact h_left_next_ge (seq_g n) (h_seq_g_left n)
  have h_seq_g_A : ∀ n, A (seq_g n) := fun n => Hereditary.of_mem_moves h_g (h_seq_g_left n)
  have h_seq_h_A : ∀ n, A (seq_h n) := fun n => Hereditary.of_mem_moves h_h (h_seq_h_right n)
  have h_bad_start : ¬ ((seq_g 0 + seq_h 0) ≥m A (0 : AugmentedForm)) := by
    intro h_ge_zero
    exact h_not_exists (seq_h 0) (h_seq_h_right 0) (MisereEq.of_antisymm h_ge_zero (h_seq_ge_zero 0))
  exact lemma_3_6_descent h_g_simplest h_h_simplest seq_g seq_h h_seq_g_left h_seq_h_right
    h_seq_g_A h_seq_h_A (Short.finite_moves .left h_g_short) h_seq_ge_zero h_seq_next_ge_zero h_bad_start

/--
This is the right-handed form of
[Davies, Yadav (Lemma 3.6 on p. 9)][davies:InvertibilityMisereMultiverse:2024]
-/
theorem lemma_3_6_right [ShortUniverse A] {g h : AugmentedForm.{u}}
    (h_g_short : IsShort g) (h_h_short : IsShort h) (h_g : A g) (h_h : A h)
    (h_g_simplest : SimplestForm A g) (h_h_simplest : SimplestForm A h)
    (h_gh_eq_zero : (g + h) =m A 0) :
    ∀ g_right ∈ moves .right g, ∃ h_left ∈ moves .left h, (g_right + h_left) =m A 0 := by
  have h_neg_sum_eq_zero : ((-g) + (-h)) =m A 0 := by
    rw [← neg_add]; simpa [neg_zero] using misereEQ_neg_iff.mpr h_gh_eq_zero
  intro g_right h_g_right_mem
  have h_neg_g_right_mem_neg_g_left : -g_right ∈ moves .left (-g) := by
    rw [moves_neg]; exact Set.neg_mem_neg.mpr h_g_right_mem
  obtain ⟨h_left, h_h_left_mem, h_neg_g_right_h_left_eq_zero⟩ :=
    lemma_3_6 (Short.neg h_g_short) (Short.neg h_h_short)
      (ClosedUnderNeg.neg_of h_g) (ClosedUnderNeg.neg_of h_h)
      (SimplestForm.neg_iff.mp h_g_simplest) (SimplestForm.neg_iff.mp h_h_simplest)
      h_neg_sum_eq_zero (-g_right) h_neg_g_right_mem_neg_g_left
  refine ⟨-h_left, ?_, ?_⟩
  · rw [moves_neg] at h_h_left_mem; exact Set.mem_neg.mp h_h_left_mem
  · have h_neg_eq := misereEQ_neg_iff.mpr h_neg_g_right_h_left_eq_zero
    rw [neg_add, neg_neg, neg_zero] at h_neg_eq
    exact h_neg_eq

theorem misereEQ_inverse_unique [ShortUniverse A] {g h k : AugmentedForm.{u}}
    (h_h : A h) (h_k : A k)
    (h_gh_zero : (g + h) =m A 0) (h_gk_zero : (g + k) =m A 0) : h =m A k := by
  have e1 : (h + (g + k)) =m A h := by
    simpa using misereEQ_add_left (A := A) h_h h_gk_zero
  have e2 : (h + (g + k)) =m A k := by
    rw [show h + (g + k) = (g + h) + k by rw [add_comm g h, add_assoc]]
    simpa using misereEQ_add_right (A := A) h_k h_gh_zero
  exact e1.symm.trans e2

-- TODO: Move
theorem add_neg_self_eq_neg (G : AugmentedForm.{u}) : -(G + (-G)) = G + (-G) := by
  rw [neg_add, neg_neg, add_comm]

theorem conjugate_of_simplest_strong [ShortUniverse A] {g : AugmentedForm.{u}}
    (h_g_short : IsShort g)
    (h_strong_left : Form.Strong A (g + (-g)) .left)
    (h_strong_right : Form.Strong A (g + (-g)) .right)
    (h_g_options_right : ∀ gr ∈ moves .right g, (gr + (-gr)) =m A 0)
    (h_g_options_left : ∀ gl ∈ moves .left g, (gl + (-gl)) =m A 0) :
    (g + (-g)) =m A 0 := by
  have h_zero_strong : Form.Strong A (0 : AugmentedForm) .left ∧ Form.Strong A (0 : AugmentedForm) .right :=
    ⟨strong_of_isEndLike (isEndLike_of_isEnd isEnd_zero),
     strong_of_isEndLike (isEndLike_of_isEnd isEnd_zero)⟩
  have h_g_neg_g_ge_zero : (g + -g) ≥m A 0 := by
    apply Form.ComparisonSet.misereGE_iff_maintenance_proviso
      (Short.add h_g_short (Short.neg h_g_short)) Short.zero |>.2 ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      rw [moves_add, Set.mem_union, Set.mem_image, Set.mem_image] at hr
      refine Or.inr ?_
      rcases hr with ⟨gr, hgr, rfl⟩ | ⟨y, hy, rfl⟩
      · refine ⟨gr + (-gr), ?_, misereGE_of_misereEQ (h_g_options_right gr hgr)⟩
        refine add_left_mem_moves_add ?_ gr
        rw [moves_neg]; exact Set.neg_mem_neg.mpr hgr
      · obtain ⟨gl, hgl, rfl⟩ : ∃ gl ∈ moves .left g, -gl = y := by
          rw [moves_neg] at hy; exact ⟨-y, by simpa using hy, by simp⟩
        refine ⟨gl + (-gl), ?_, misereGE_of_misereEQ (h_g_options_left gl hgl)⟩
        exact add_right_mem_moves_add hgl (-gl)
    · intro l hl; simp only [moves_zero, Set.mem_empty_iff_false] at hl
    · exact fun _ => h_zero_strong.2
    · exact fun _ => h_strong_left
  have h_zero_ge_g_neg_g : (0 : AugmentedForm) ≥m A (g + -g) := by
    apply Form.ComparisonSet.misereGE_iff_maintenance_proviso
      Short.zero (Short.add h_g_short (Short.neg h_g_short)) |>.2 ⟨?_, ?_, ?_, ?_⟩
    · intro r hr; simp only [moves_zero, Set.mem_empty_iff_false] at hr
    · intro l hl
      rw [moves_add, Set.mem_union, Set.mem_image, Set.mem_image] at hl
      refine Or.inr ?_
      rcases hl with ⟨gl, hgl, rfl⟩ | ⟨y, hy, rfl⟩
      · refine ⟨gl + (-gl), ?_, misereGE_of_misereEQ (h_g_options_left gl hgl).symm⟩
        refine add_left_mem_moves_add ?_ gl
        rw [moves_neg]; exact Set.neg_mem_neg.mpr hgl
      · obtain ⟨gr, hgr, rfl⟩ : ∃ gr ∈ moves .right g, -gr = y := by
          rw [moves_neg] at hy; exact ⟨-y, by simpa using hy, by simp⟩
        refine ⟨gr + (-gr), ?_, misereGE_of_misereEQ (h_g_options_right gr hgr).symm⟩
        exact add_right_mem_moves_add hgr (-gr)
    · exact fun _ => h_strong_right
    · exact fun _ => h_zero_strong.1
  exact MisereEq.of_antisymm h_g_neg_g_ge_zero h_zero_ge_g_neg_g

theorem misereGE_zero_iff_zero_misereGE [ShortUniverse A] {g : AugmentedForm.{u}} :
    ((g + (-g)) ≥m A 0) ↔ ((0 : AugmentedForm) ≥m A (g + (-g))) := by
  have h1 := ClosedUnderNeg.neg_ge_neg_iff (A := A) (g + (-g)) 0
  simpa [neg_zero, add_neg_self_eq_neg] using h1.symm

theorem neg_inverse_options_match [ShortUniverse A] {g h : AugmentedForm.{u}}
    (h_g_short : IsShort g) (h_h_short : IsShort h) (h_g : A g) (h_h : A h)
    (h_g_simplest : SimplestForm A g) (h_h_simplest : SimplestForm A h)
    (h_gh_eq_zero : (g + h) =m A 0)
    (h_g_options : ∀ p, ∀ g' ∈ moves p g, (g' + (-g')) =m A 0) :
    (∀ x ∈ moves .left (-g), ∃ y ∈ moves .left h, x =m A y) ∧
    (∀ y ∈ moves .left h, ∃ x ∈ moves .left (-g), x =m A y) ∧
    (∀ x ∈ moves .right (-g), ∃ y ∈ moves .right h, x =m A y) ∧
    (∀ y ∈ moves .right h, ∃ x ∈ moves .right (-g), x =m A y) := by
  refine' ⟨ _, _, _, _ ⟩
  · intro x h_x_mem_neg_g_left
    obtain ⟨g_right, h_g_right_mem, h_x_eq⟩ : ∃ g_right ∈ moves .right g, x = -g_right := by
      refine ⟨-x, ?_, (neg_neg x).symm⟩
      rw [moves_neg] at h_x_mem_neg_g_left
      exact Set.mem_neg.mp h_x_mem_neg_g_left
    obtain ⟨h_left, h_h_left_mem, h_gh_left_eq_zero⟩ :
        ∃ h_left ∈ moves .left h, (g_right + h_left) =m A 0 := by
      convert lemma_3_6_right h_g_short h_h_short h_g h_h h_g_simplest h_h_simplest
        h_gh_eq_zero g_right h_g_right_mem using 1
    have h_x_eq_h_left : x =m A h_left := by
      have h_h_left_eq_neg_g_right : h_left =m A (-g_right) := by
        apply misereEQ_inverse_unique
        exact Hereditary.of_mem_moves h_h h_h_left_mem
        exact ClosedUnderNeg.neg_of (Hereditary.of_mem_moves h_g h_g_right_mem)
        exact h_gh_left_eq_zero
        exact h_g_options _ _ h_g_right_mem
      exact h_x_eq.symm ▸ h_h_left_eq_neg_g_right.symm
    exact ⟨h_left, h_h_left_mem, h_x_eq_h_left⟩
  · intro h_left h_h_left_mem
    obtain ⟨g_right, h_g_right_mem, h_g_right_eq_h_left⟩ :=
      lemma_3_6 h_h_short h_g_short h_h h_g h_h_simplest h_g_simplest
        (by simpa only [add_comm] using h_gh_eq_zero) h_left h_h_left_mem
    have h_g_right_conj_zero : (g_right + (-g_right)) =m A 0 :=
      h_g_options _ _ h_g_right_mem
    have h_h_left_eq_neg_g_right : h_left =m A (-g_right) := by
      apply misereEQ_inverse_unique
      exact Hereditary.of_mem_moves h_h h_h_left_mem
      exact ClosedUnderNeg.neg_of (Hereditary.of_mem_moves h_g h_g_right_mem)
      convert h_g_right_eq_h_left using 1
      rw [add_comm]
      exact h_g_right_conj_zero
    use -g_right
    refine ⟨?_, MisereEQ.symm h_h_left_eq_neg_g_right⟩
    rw [moves_neg]
    exact Set.neg_mem_neg.mpr h_g_right_mem
  · intro x h_x_mem_neg_g_right
    rw [moves_neg] at h_x_mem_neg_g_right
    have h_neg_x_mem_left_g : -x ∈ moves .left g := Set.mem_neg.mp h_x_mem_neg_g_right
    obtain ⟨h_left, h_h_left_mem, h_h_left_eq_neg_x⟩ :=
      lemma_3_6 h_g_short h_h_short h_g h_h h_g_simplest h_h_simplest
        h_gh_eq_zero (-x) h_neg_x_mem_left_g
    refine ⟨h_left, h_h_left_mem, ?_⟩
    have h_A_neg_x : A (-x) := Hereditary.of_mem_moves h_g h_neg_x_mem_left_g
    have h_A_x : A x := by simpa using ClosedUnderNeg.neg_of h_A_neg_x
    have h_x_neg_x_zero : ((-x) + x) =m A 0 := by
      have h_conj := h_g_options .left (-x) h_neg_x_mem_left_g
      rwa [neg_neg] at h_conj
    exact misereEQ_inverse_unique h_A_x (Hereditary.of_mem_moves h_h h_h_left_mem)
      h_x_neg_x_zero h_h_left_eq_neg_x
  · intro h_right h_h_right_mem
    obtain ⟨g_left, h_g_left_mem, h_g_left_eq_h_right⟩ :
        ∃ g_left ∈ moves .left g, (h_right + g_left) =m A 0 := by
      have := @lemma_3_6_right A
      convert this h_h_short h_g_short h_h h_g h_h_simplest h_g_simplest
        (by simpa only [add_comm] using h_gh_eq_zero) h_right h_h_right_mem using 1
    have h_neg_g_left_eq_h_right : (-g_left) =m A h_right := by
      apply misereEQ_inverse_unique
      exact ClosedUnderNeg.neg_of (Hereditary.of_mem_moves h_g h_g_left_mem)
      exact Hereditary.of_mem_moves h_h h_h_right_mem
      exact h_g_options .left g_left h_g_left_mem
      rwa [add_comm]
    use -g_left
    simp [moves_neg, h_g_left_mem, h_neg_g_left_eq_h_right]

-- TODO: Move
theorem isEndLike_symmetric_of_both_tombstones {g : AugmentedForm.{u}} (p : Player)
    (h_tomb_L : g.hasTombstone .left) (h_tomb_R : g.hasTombstone .right) :
    IsEndLike p (g + (-g)) := by
  rw [IsEndLike_iff]
  refine Or.inl ?_
  rw [hasTombstone_add]
  refine Or.inl ⟨?_, ?_⟩
  · cases p <;> assumption
  · rw [IsEndLike_iff]
    refine Or.inl ?_
    rw [hasTombstone_neg_iff]
    cases p <;> simpa using ‹_›

theorem conjugate_eq_zero_of_both_tombstones [ShortUniverse A] {g : AugmentedForm.{u}}
    (h_short : IsShort g) (h_tomb_L : g.hasTombstone .left) (h_tomb_R : g.hasTombstone .right)
    (h_moves : ∀ p, ∀ g' ∈ moves p g, (g' + (-g')) =m A 0) :
    (g + (-g)) =m A 0 :=
  conjugate_of_simplest_strong h_short
    (strong_of_isEndLike (isEndLike_symmetric_of_both_tombstones .left h_tomb_L h_tomb_R))
    (strong_of_isEndLike (isEndLike_symmetric_of_both_tombstones .right h_tomb_L h_tomb_R))
    (h_moves .right) (h_moves .left)

theorem option_conjugate_of_matching [ShortUniverse A] {g h : AugmentedForm.{u}}
    (h_g_short : IsShort g) (h_h_short : IsShort h) (h_g : A g) (h_h : A h)
    (h_g_simplest : SimplestForm A g) (h_h_simplest : SimplestForm A h)
    (h_gh_eq_zero : (g + h) =m A 0)
    (h_g_options : ∀ p, ∀ g' ∈ moves p g, (g' + (-g')) =m A 0) :
    ∀ p, ∀ h' ∈ moves p h, (h' + (-h')) =m A 0 := by
  obtain ⟨_, h_left_match_H_to_negG, _, h_right_match_H_to_negG⟩ :=
    neg_inverse_options_match h_g_short h_h_short h_g h_h h_g_simplest h_h_simplest h_gh_eq_zero h_g_options
  intro p h' h_h'_mem
  have h_neg_g_exists : ∃ x ∈ moves p (-g), x =m A h' := by
    cases p
    · exact h_left_match_H_to_negG h' h_h'_mem
    · exact h_right_match_H_to_negG h' h_h'_mem
  obtain ⟨x, h_x_mem, h_x_eq_h'⟩ := h_neg_g_exists
  obtain ⟨g', h_g'_mem, h_neg_g'_eq_x⟩ : ∃ g' ∈ moves (-p) g, -g' = x := by
    rw [moves_neg, Set.mem_neg] at h_x_mem
    exact ⟨-x, h_x_mem, neg_neg x⟩
  subst h_neg_g'_eq_x
  have h_g' : A g' := Hereditary.of_mem_moves h_g h_g'_mem
  have h_h'_eq_neg_g' : h' =m A (-g') := h_x_eq_h'.symm
  have step1 : (h' + (-h')) =m A ((-g') + (-h')) :=
    misereEQ_add_right (A := A) (ClosedUnderNeg.neg_of (Hereditary.of_mem_moves h_h h_h'_mem)) h_h'_eq_neg_g'
  have h_neg_h'_eq_g' : (-h') =m A g' := by
    have := misereEQ_neg_iff.mpr h_h'_eq_neg_g'
    simpa using this
  have step2 : ((-g') + (-h')) =m A ((-g') + g') :=
    misereEQ_add_left (A := A) (ClosedUnderNeg.neg_of h_g') h_neg_h'_eq_g'
  have step3 : ((-g') + g') =m A 0 := by
    rw [add_comm]
    exact h_g_options (-p) g' h_g'_mem
  exact (step1.trans step2).trans step3

theorem misereGE_of_matching_tombstones [ShortUniverse A] {x y : AugmentedForm.{u}}
    (h_left_match_x_to_y : ∀ xl ∈ moves .left x, ∃ yl ∈ moves .left y, xl =m A yl)
    (h_left_match_y_to_x : ∀ yl ∈ moves .left y, ∃ xl ∈ moves .left x, yl =m A xl)
    (h_right_match_x_to_y : ∀ xr ∈ moves .right x, ∃ yr ∈ moves .right y, xr =m A yr)
    (h_right_match_y_to_x : ∀ yr ∈ moves .right y, ∃ xr ∈ moves .right x, yr =m A xr)
    (h_tombstone_left_impl : y.hasTombstone .left → x.hasTombstone .left)
    (h_tombstone_right_impl : x.hasTombstone .right → y.hasTombstone .right) :
    x ≥m A y := by
  apply Hereditary.misereGE_of_maintenance_proviso
  · intro xr h_xr
    obtain ⟨yr, h_yr, he⟩ := h_right_match_x_to_y xr h_xr
    exact Or.inl ⟨yr, h_yr, misereGE_of_misereEQ he⟩
  · intro yl h_yl
    obtain ⟨xl, h_xl, he⟩ := h_left_match_y_to_x yl h_yl
    exact Or.inl ⟨xl, h_xl, misereGE_of_misereEQ he.symm⟩
  · intro h_xe
    by_cases h_xR : x.hasTombstone .right
    · exact strong_of_isEndLike (IsEndLike_iff.mpr (Or.inl (h_tombstone_right_impl h_xR)))
    · have h_xend : Form.IsEnd .right x := (IsEndLike_iff.mp h_xe).resolve_left h_xR
      have h_yend : Form.IsEnd .right y := by
        apply isEnd_of_not_mem
        intro yr h_yr
        obtain ⟨xr, h_xr, _⟩ := h_right_match_y_to_x yr h_yr
        exact (not_mem_moves_of_isEnd h_xend) h_xr
      exact strong_of_isEndLike (IsEndLike_iff.mpr (Or.inr h_yend))
  · intro h_ye
    by_cases h_yL : y.hasTombstone .left
    · exact strong_of_isEndLike (IsEndLike_iff.mpr (Or.inl (h_tombstone_left_impl h_yL)))
    · have h_yend : Form.IsEnd .left y := (IsEndLike_iff.mp h_ye).resolve_left h_yL
      have h_xend : Form.IsEnd .left x := by
        apply isEnd_of_not_mem
        intro xl h_xl
        obtain ⟨yl, h_yl, _⟩ := h_left_match_x_to_y xl h_xl
        exact (not_mem_moves_of_isEnd h_yend) h_yl
      exact strong_of_isEndLike (IsEndLike_iff.mpr (Or.inr h_xend))

theorem tombstone_dichotomy [ShortUniverse A] {g h : AugmentedForm.{u}}
    (h_g_short : IsShort g) (h_h_short : IsShort h) (h_g : A g) (h_h : A h)
    (h_g_simplest : SimplestForm A g) (h_h_simplest : SimplestForm A h)
    (h_gh_eq_zero : (g + h) =m A 0)
    (h_g_options : ∀ p, ∀ g' ∈ moves p g, (g' + (-g')) =m A 0)
    (h_not_comparable : ¬ ((-g) ≥m A h) ∧ ¬ (h ≥m A (-g))) :
    (g.hasTombstone .left ∧ g.hasTombstone .right) ∨
    (h.hasTombstone .left ∧ h.hasTombstone .right) := by
  obtain ⟨h_match_left, h_match_right, h_match_left_rev, h_match_right_rev⟩ :=
    neg_inverse_options_match h_g_short h_h_short h_g h_h h_g_simplest h_h_simplest h_gh_eq_zero h_g_options
  obtain ⟨h_not_ge_neg_g_h, h_not_ge_h_neg_g⟩ := h_not_comparable
  have h_impl_ge_neg_g_h :
      (h.hasTombstone .left → (-g).hasTombstone .left) →
      ((-g).hasTombstone .right → h.hasTombstone .right) →
      ((-g) ≥m A h) := by
    intro h_left_impl h_right_impl
    refine misereGE_of_matching_tombstones h_match_left ?_ h_match_left_rev ?_ h_left_impl h_right_impl
    · intro yl h_yl; obtain ⟨xl, h_xl, he⟩ := h_match_right yl h_yl; exact ⟨xl, h_xl, he.symm⟩
    · intro yr h_yr; obtain ⟨xr, h_xr, he⟩ := h_match_right_rev yr h_yr; exact ⟨xr, h_xr, he.symm⟩
  have h_impl_ge_h_neg_g :
      ((-g).hasTombstone .left → h.hasTombstone .left) →
      (h.hasTombstone .right → (-g).hasTombstone .right) →
      (h ≥m A (-g)) := by
    intro h_left_impl h_right_impl
    refine misereGE_of_matching_tombstones ?_ ?_ ?_ ?_ h_left_impl h_right_impl
    · intro xl h_xl; obtain ⟨yl, h_yl, he⟩ := h_match_right xl h_xl; exact ⟨yl, h_yl, he.symm⟩
    · intro yl h_yl; obtain ⟨xl, h_xl, he⟩ := h_match_left yl h_yl; exact ⟨xl, h_xl, he⟩
    · intro xr h_xr; obtain ⟨yr, h_yr, he⟩ := h_match_right_rev xr h_xr; exact ⟨yr, h_yr, he.symm⟩
    · intro yr h_yr; obtain ⟨xr, h_xr, he⟩ := h_match_left_rev yr h_yr; exact ⟨xr, h_xr, he⟩
  have h_neg_g_tombstone_left_iff_g_tombstone_right :
      (-g).hasTombstone .left ↔ g.hasTombstone .right := by
    simpa using (hasTombstone_neg_iff (g := g) (p := .left))
  have h_neg_g_tombstone_right_iff_g_tombstone_left :
      (-g).hasTombstone .right ↔ g.hasTombstone .left := by
    simpa using (hasTombstone_neg_iff (g := g) (p := .right))
  tauto

theorem conjugate_incomparable [ShortUniverse A] {g h : AugmentedForm.{u}}
    (h_g_short : IsShort g) (h_h_short : IsShort h) (h_g : A g) (h_h : A h)
    (h_g_simplest : SimplestForm A g) (h_h_simplest : SimplestForm A h)
    (h_gh_eq_zero : (g + h) =m A 0)
    (h_g_options : ∀ p, ∀ g' ∈ moves p g,
      ((g' + (-g')) =m A 0) ∧ Form.Strong A (g' + (-g')) .left ∧ Form.Strong A (g' + (-g')) .right)
    (h_not_comparable : ¬ ((-g) ≥m A h) ∧ ¬ (h ≥m A (-g))) :
    (g + (-g)) =m A 0 := by
  have h_g_options_eq : ∀ p, ∀ g' ∈ moves p g, (g' + (-g')) =m A 0 :=
    fun p g' hg' => (h_g_options p g' hg').1
  rcases tombstone_dichotomy h_g_short h_h_short h_g h_h h_g_simplest h_h_simplest
      h_gh_eq_zero h_g_options_eq h_not_comparable with
    ⟨h_g_left, h_g_right⟩ | ⟨h_h_left, h_h_right⟩
  · exact conjugate_eq_zero_of_both_tombstones h_g_short h_g_left h_g_right h_g_options_eq
  · have h_h_options_eq : ∀ p, ∀ h' ∈ moves p h, (h' + (-h')) =m A 0 :=
      option_conjugate_of_matching h_g_short h_h_short h_g h_h h_g_simplest h_h_simplest h_gh_eq_zero h_g_options_eq
    have h_h_neg_h_eq_zero : (h + (-h)) =m A 0 :=
      conjugate_eq_zero_of_both_tombstones h_h_short h_h_left h_h_right h_h_options_eq
    have h_hg_eq_zero : (h + g) =m A 0 := by rwa [add_comm]
    have h_g_eq_neg_h : g =m A (-h) :=
      misereEQ_inverse_unique h_g (ClosedUnderNeg.neg_of h_h) h_hg_eq_zero h_h_neg_h_eq_zero
    have h_neg_g_eq_h : (-g) =m A h := by
      have := misereEQ_neg_iff.mpr h_g_eq_neg_h
      simpa using this
    have step1 : (g + (-g)) =m A ((-h) + (-g)) :=
      misereEQ_add_right (A := A) (ClosedUnderNeg.neg_of h_g) h_g_eq_neg_h
    have step2 : ((-h) + (-g)) =m A ((-h) + h) :=
      misereEQ_add_left (A := A) (ClosedUnderNeg.neg_of h_h) h_neg_g_eq_h
    have step3 : ((-h) + h) =m A 0 := by rw [add_comm]; exact h_h_neg_h_eq_zero
    exact (step1.trans step2).trans step3

theorem conjugate_of_simplest_aux [ShortUniverse A] {g : AugmentedForm.{u}}
    (h_g_short : IsShort g) (h_g : A g) (h_g_simplest : SimplestForm A g)
    (h_h_exist : ∃ h, IsShort h ∧ A h ∧ SimplestForm A h ∧ (g + h) =m A 0) :
    ((g + (-g)) =m A 0) ∧ Form.Strong A (g + (-g)) .left ∧ Strong A (g + (-g)) .right := by
  obtain ⟨h, h_h_short, h_h, h_h_simplest, h_gh_eq_zero⟩ := h_h_exist
  have h_g_options : ∀ p, ∀ g' ∈ moves p g,
      ((g' + (-g')) =m A 0) ∧ Form.Strong A (g' + (-g')) .left ∧ Strong A (g' + (-g')) .right := by
    intro p g' h_g'_mem
    have h_g'_short : IsShort g' := Short.of_mem_moves h_g_short h_g'_mem
    have h_g' : A g' := Hereditary.of_mem_moves h_g h_g'_mem
    have h_g'_simplest : SimplestForm A g' := h_g_simplest.of_mem_moves h_g'_mem
    have h_h'_inv : ∃ h', IsShort h' ∧ A h' ∧ SimplestForm A h' ∧ (g' + h') =m A 0 := by
      cases p
      · obtain ⟨hr, hhr, he⟩ := lemma_3_6 h_g_short h_h_short h_g h_h h_g_simplest h_h_simplest h_gh_eq_zero g' h_g'_mem
        exact ⟨hr, Short.of_mem_moves h_h_short hhr, Hereditary.of_mem_moves h_h hhr, h_h_simplest.of_mem_moves hhr, he⟩
      · obtain ⟨hl, hhl, he⟩ := lemma_3_6_right h_g_short h_h_short h_g h_h h_g_simplest h_h_simplest h_gh_eq_zero g' h_g'_mem
        exact ⟨hl, Short.of_mem_moves h_h_short hhl, Hereditary.of_mem_moves h_h hhl, h_h_simplest.of_mem_moves hhl, he⟩
    exact conjugate_of_simplest_aux h_g'_short h_g' h_g'_simplest h_h'_inv
  have h_g_neg_g_ge_zero : (g + (-g)) ≥m A 0 := by
    by_cases h_comp : ((-g) ≥m A h) ∨ (h ≥m A (-g))
    · rcases h_comp with h1 | h1
      · have h_step : ((-g) + g) ≥m A (h + g) := misereGE_add_right h_g h1
        have h_step' : (g + (-g)) ≥m A (g + h) := by rwa [add_comm g (-g), add_comm g h]
        exact MisereGE.trans h_step' (misereGE_of_misereEQ h_gh_eq_zero)
      · have h_step : (h + g) ≥m A ((-g) + g) := misereGE_add_right h_g h1
        have h_step' : (g + h) ≥m A (g + (-g)) := by rwa [add_comm g (-g), add_comm g h]
        have h0 : (0 : AugmentedForm) ≥m A (g + (-g)) :=
          MisereGE.trans (misereGE_of_misereEQ h_gh_eq_zero.symm) h_step'
        exact misereGE_zero_iff_zero_misereGE.mpr h0
    · push_neg at h_comp
      exact misereGE_of_misereEQ (conjugate_incomparable h_g_short h_h_short h_g h_h h_g_simplest h_h_simplest h_gh_eq_zero h_g_options h_comp)
  have h_zero_ge : (0 : AugmentedForm) ≥m A (g + (-g)) := misereGE_zero_iff_zero_misereGE.mp h_g_neg_g_ge_zero
  have h_strong_L : Form.Strong A (g + (-g)) .left :=
    proviso_left_of_misereGE h_g_neg_g_ge_zero (isEndLike_of_isEnd isEnd_zero)
  have h_strong_R : Form.Strong A (g + (-g)) .right :=
    proviso_right_of_misereGE h_zero_ge (isEndLike_of_isEnd isEnd_zero)
  have h_eq_zero : (g + (-g)) =m A 0 := MisereEq.of_antisymm h_g_neg_g_ge_zero h_zero_ge
  exact ⟨h_eq_zero, h_strong_L, h_strong_R⟩
termination_by g
decreasing_by form_wf

theorem conjugate_of_simplest [ShortUniverse A] {G H : AugmentedForm.{u}}
    (hG : IsShort G) (hH : IsShort H) (hAG : A G) (hAH : A H)
    (hsG : SimplestForm A G) (hsH : SimplestForm A H)
    (hsum : (G + H) =m A 0) : (G + (-G)) =m A 0 :=
  (conjugate_of_simplest_aux hG hAG hsG ⟨H, hH, hAH, hsH, hsum⟩).1

/--
$H$ is an $\mathcal{A}$-inverse of $G$ if $G \in \mathcal{A}$ and $G + H =_{\mathcal{A}} 0$.

This is [Davies, Yadav (Definition 3.1 on p. 8)][davies:InvertibilityMisereMultiverse:2024]
-/
@[expose] def IsInverse {G : Type (u + 1)} [Form G] (A : G → Prop) (g h : G) : Prop :=
  A h ∧ ((g + h) =m A 0)

/--
$G$ is $\mathcal{A}$-invertible if it has some $\mathcal{A}$-inverse.

This is [Davies, Yadav (Definition 3.1 on p. 8)][davies:InvertibilityMisereMultiverse:2024]
-/
@[expose] def Invertible {G : Type (u + 1)} [Form G] (A : G → Prop) (g : G) : Prop :=
  ∃ h, IsInverse A g h

/--
$G$ is conjugate $\mathcal{A}$-invertible if $\overline{G}$ is an $\mathcal{A}$-inverse of $G$.

This is [Davies, Yadav (Definition 3.2 on p. 8)][davies:InvertibilityMisereMultiverse:2024]
-/
@[expose] def ConjugateInvertible {G : Type (u + 1)} [Form G] (A : G → Prop) (g : G) : Prop :=
  IsInverse A g (-g)

/--
This is [Davies, Yadav (Definition 3.5 on p. 9)][davies:InvertibilityMisereMultiverse:2024]
-/
@[expose] def ConjugateProperty {G : Type (u + 1)} [Form G] (A : G → Prop) : Prop :=
  ∀ g, A g → Invertible A g → ConjugateInvertible A g

/--
This is the augmented-form version of
[Davies, Yadav (Theorem 3.7 on p. 11)][davies:InvertibilityMisereMultiverse:2024]
-/
theorem conjugateProperty_of_closedSimplest [ShortUniverse A]
    (hSF : ∀ g, A g → ∃ k, A k ∧ IsShort k ∧ SimplestForm A k ∧ (k =m A g)) :
    ConjugateProperty A := by
  rintro g h_g ⟨h, h_h, h_gh_eq_zero⟩
  refine ⟨ClosedUnderNeg.neg_of h_g, ?_⟩
  obtain ⟨g', h_g', h_g'_short, h_g'_simplest, h_g'_eq⟩ := hSF g h_g
  obtain ⟨h', h_h', h_h'_short, h_h'_simplest, h_h'_eq⟩ := hSF h h_h
  have h_g'h'_eq_zero : (g' + h') =m A 0 := by
    have h1 : (g' + h') =m A (g + h') := misereEQ_add_right h_h' h_g'_eq
    have h2 : (g + h') =m A (g + h) := misereEQ_add_left h_g h_h'_eq
    exact (h1.trans h2).trans h_gh_eq_zero
  have h_g'_inv : (g' + (-g')) =m A 0 :=
    conjugate_of_simplest h_g'_short h_h'_short h_g' h_h' h_g'_simplest h_h'_simplest h_g'h'_eq_zero
  have h_g_inv : (g + (-g)) =m A (g' + (-g')) := by
    have h1 : (g + (-g)) =m A (g' + (-g)) :=
      misereEQ_add_right (ClosedUnderNeg.neg_of h_g) h_g'_eq.symm
    have h2 : (g' + (-g)) =m A (g' + (-g')) :=
      misereEQ_add_left h_g' (misereEQ_neg_iff.mpr h_g'_eq.symm)
    exact h1.trans h2
  exact h_g_inv.trans h_g'_inv

/--
This is [Siegel (Definition 5.20 on p. 220)][siegel:GeneralDeadendingUniverse:2025]
together with [Siegel (Theorem 5.22 on p. 220)][siegel:GeneralDeadendingUniverse:2025].
-/
theorem exists_augmented_universe (A : GameForm.{u} → Prop) [ShortUniverse A] :
    ∃ (U' : AugmentedForm.{u} → Prop), ShortUniverse U' ∧
      (∀ a : GameForm.{u}, A a → U' (ofGameForm a)) ∧
      (∀ p q : GameForm.{u}, A p → A q → ((ofGameForm p =m U' ofGameForm q) ↔ p =m A q)) ∧
      (∀ g, U' g → ∃ k, U' k ∧ IsShort k ∧ SimplestForm U' k ∧ (k =m U' g)) :=
  ⟨ExpansionSet A, inferInstance, expansionSet_mem_ofGameForm,
    fun _ _ hp hq => expansionSet_misereEQ_iff hp hq, expansionSet_closedSimplest⟩

/-- 
This is [Davies, Yadav (Theorem 3.7 on p. 11)][davies:InvertibilityMisereMultiverse:2024]
-/
theorem conjugateProperty_of_shortUniverse {A : GameForm.{u} → Prop} [ShortUniverse A] :
    ConjugateProperty A := by
  obtain ⟨U', h_U'_uni, h_mem, h_iff_eq, h_simplest⟩ := AugmentedForm.exists_augmented_universe A
  intro g h_g h_g_inv
  obtain ⟨h, h_h, h_gh_eq_zero⟩ := h_g_inv
  have h_0 : A (0 : GameForm.{u}) := ‹ShortUniverse A›.zero_mem
  have h_gh : A (g + h) := ClosedUnderAdd.has_add g h h_g h_h
  have h_g_neg_g : A (g + (-g)) := ClosedUnderAdd.has_add g (-g) h_g (ClosedUnderNeg.neg_of h_g)
  have h_g_aug : U' (ofGameForm g) := h_mem g h_g
  have h_inv_aug : Invertible U' (ofGameForm g) := by
    refine ⟨ofGameForm h, h_mem h h_h, ?_⟩
    have h_gh_eq_zero_aug : (ofGameForm (g + h)) =m U' (ofGameForm 0) :=
      (h_iff_eq (g + h) 0 h_gh h_0).mpr h_gh_eq_zero
    rwa [ofGameForm_add, ofGameForm_zero] at h_gh_eq_zero_aug
  have h_conj : ConjugateProperty U' := conjugateProperty_of_closedSimplest h_simplest
  have h_conj_aug : ConjugateInvertible U' (ofGameForm g) := h_conj _ h_g_aug h_inv_aug
  refine ⟨ClosedUnderNeg.neg_of h_g, ?_⟩
  have h_sub_eq_zero : (ofGameForm g + -(ofGameForm g)) =m U' 0 := h_conj_aug.right
  rw [←ofGameForm_neg, ←ofGameForm_add, ←ofGameForm_zero] at h_sub_eq_zero
  exact (h_iff_eq (g + (-g)) 0 h_g_neg_g h_0).mp h_sub_eq_zero

end AugmentedForm
