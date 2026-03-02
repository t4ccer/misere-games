module

public import CombinatorialGames.GameForm.Misere.Outcome

public section

namespace Form

universe u

variable {G : Type (u + 1)} [g_form : Form G]

open Form

def IsDeadEnd (p : Player) (g : G) : Prop :=
  IsEnd p g ∧ (∀ gp ∈ moves (-p) g, IsDeadEnd p gp)
termination_by g
decreasing_by form_wf

def IsDeadEnd_IsEnd {g : G} {p : Player} (h1 : IsDeadEnd p g) : IsEnd p g := by
  unfold IsDeadEnd at h1
  exact h1.left

def IsDeadEnd_moves {g : G} {p : Player} (h1 : IsDeadEnd p g) :
    ∀ gp ∈ moves (-p) g, IsDeadEnd p gp := by
  unfold IsDeadEnd at h1
  exact h1.right

theorem IsDeadEnd.add {g h : G} {p : Player} (h1 : IsDeadEnd p g) (h2 : IsDeadEnd p h) :
    IsDeadEnd p (g + h) := by
  unfold IsDeadEnd
  simp only [moves_add, Set.mem_union, Set.mem_image]
  apply And.intro (IsEnd.add_iff.mpr ⟨IsDeadEnd_IsEnd h1, IsDeadEnd_IsEnd h2⟩)
  intro gp h3
  apply Or.elim h3 <;> intro ⟨gpp, h3, h4⟩ <;> rw [<-h4]
  · exact IsDeadEnd.add (IsDeadEnd_moves h1 gpp h3) h2
  · exact IsDeadEnd.add h1 (IsDeadEnd_moves h2 gpp h3)
termination_by (g, h)
decreasing_by all_goals form_wf

private theorem IsDeadEnd.neg {g : G} {p : Player} (h1 : IsDeadEnd p (-g)) : IsDeadEnd (-p) g := by
  have h0 := h1
  unfold IsDeadEnd at h1 ⊢
  have ⟨h3, h2⟩ := h1
  apply And.intro (IsEnd_neg_iff_neg.mp h3)
  rw [neg_neg]
  intro gp h4
  have h5 : IsDeadEnd p (-gp) := by
    rw [<-neg_neg g, moves_neg] at h4
    exact h2 (-gp) (Set.mem_neg.mp h4)
  exact IsDeadEnd.neg h5
termination_by g
decreasing_by form_wf

@[simp]
theorem IsDeadEnd.neg_iff {g : G} {p : Player} : IsDeadEnd p (-g) ↔ IsDeadEnd (-p) g := by
  constructor <;> intro h1
  · exact IsDeadEnd.neg h1
  · rw [<-neg_neg g] at h1
    rw [<-neg_neg p]
    exact IsDeadEnd.neg h1

@[simp]
theorem IsDeadEnd.zero {p : Player} : IsDeadEnd p (0 : GameForm) := by
  unfold IsDeadEnd
  simp only [IsEnd_zero, moves_zero, Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true,
             and_self]

@[simp]
theorem IsDeadEnd.right_nat (n : ℕ) : IsDeadEnd .right (n : GameForm) := by
  match n with
  | .zero => exact IsDeadEnd.zero
  | .succ k => unfold IsDeadEnd; simp [IsDeadEnd.right_nat k]

@[simp]
theorem IsDeadEnd.right_nonneg_int (k : ℤ) (h1 : k ≥ 0) : IsDeadEnd .right (k : GameForm) := by
  rw [<-Int.toNat_of_nonneg h1]
  norm_cast
  simp only [IsDeadEnd.right_nat]

@[simp]
theorem IsDeadEnd.left_nonpos_int (k : ℤ) (h1 : k ≤ 0) : IsDeadEnd .left (k : GameForm) := by
  rw [<-Player.neg_right, <-IsDeadEnd.neg_iff]
  norm_cast
  exact IsDeadEnd.right_nonneg_int (-k) (by omega)

def IsDeadEnding (g : G) : Prop :=
  (∀ p, IsEnd p g → IsDeadEnd p g) ∧ (∀ p, ∀gp ∈ moves p g, IsDeadEnding gp)
termination_by g
decreasing_by form_wf

@[simp]
theorem IsDeadEnding.IsDeadEnd {g : G} {p : Player} (h1 : IsDeadEnding g) (h2 : IsEnd p g) :
    IsDeadEnd p g := by
  unfold IsDeadEnding at h1
  exact h1.left p h2

@[simp]
theorem IsDeadEnding.moves {g h : G} {p : Player} (h1 : IsDeadEnding g) (h2 : h ∈ moves p g) :
    IsDeadEnding h := by
  unfold IsDeadEnding at h1
  exact h1.right p h h2

end Form

namespace GameForm

open GameForm.Misere.Outcome
open Form
open Form.Misere.Outcome

private theorem lemma3.aux {g : GameForm} {p : Player} (h1 : g ≠ 0) (h2 : IsDeadEnd p g) :
    MisereForm.MisereOutcome g = Outcome.ofPlayer p := by
  rw [MisereOutcome_eq_player_iff]
  apply And.intro (WinsGoingFirst_of_End (IsDeadEnd_IsEnd h2))
  simp only [not_WinsGoingFirst, neg_neg]
  apply And.intro (zero_not_both_end h1 (IsDeadEnd_IsEnd h2))
  intro gr h4
  exact WinsGoingFirst_of_End (IsDeadEnd_IsEnd (IsDeadEnd_moves h2 gr h4))

theorem lemma3_L (g : GameForm) (h1 : g ≠ 0) (h2 : IsDeadEnd .left g) :
    MisereForm.MisereOutcome g = .L := lemma3.aux h1 h2

theorem lemma3_R (g : GameForm) (h1 : g ≠ 0) (h2 : IsDeadEnd .right g) :
    MisereForm.MisereOutcome g = .R := lemma3.aux h1 h2

@[simp]
theorem IsDeadEnding.add {g h : GameForm} (h1 : IsDeadEnding g) (h2 : IsDeadEnding h) :
    IsDeadEnding (g + h) := by
  unfold IsDeadEnding
  simp only [moves_add, Set.mem_union, Set.mem_image]
  constructor <;> intro p
  · intro h3
    have ⟨h4, h5⟩ := IsEnd.add_iff.mp h3
    exact IsDeadEnd.add (IsDeadEnding.IsDeadEnd h1 h4) (IsDeadEnding.IsDeadEnd h2 h5)
  · intro gp h3
    apply Or.elim h3 <;> intro ⟨g', h3, h4⟩ <;> rw [<-h4]
    · exact IsDeadEnding.add (IsDeadEnding.moves h1 h3) h2
    · exact IsDeadEnding.add h1 (IsDeadEnding.moves h2 h3)
termination_by (g, h)
decreasing_by all_goals form_wf

private theorem IsDeadEnding.neg {g : GameForm} (h1 : IsDeadEnding (-g)) : IsDeadEnding g := by
  unfold IsDeadEnding at h1 ⊢
  obtain ⟨h1, h2⟩ := h1
  apply And.intro
  · intro p h3
    rw [<-neg_neg p, <-IsEnd_neg_iff_neg] at h3
    have h4 := IsDeadEnd.neg_iff.mp (h1 (-p) h3)
    rwa [neg_neg] at h4
  · intro p gp h3
    have h4 := h2 (-p) (-gp) (by simp [h3])
    exact IsDeadEnding.neg h4
termination_by g
decreasing_by form_wf

@[simp]
theorem IsDeadEnding.neg_iff {g : GameForm} : IsDeadEnding (-g) ↔ IsDeadEnding g := by
  constructor <;> intro h1
  · exact IsDeadEnding.neg h1
  · rw [<-neg_neg g] at h1
    exact IsDeadEnding.neg h1

@[simp]
theorem IsDeadEnding.zero : IsDeadEnding (0 : GameForm) := by
  unfold IsDeadEnding IsDeadEnd
  simp only [IsEnd_zero, moves_zero, Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true,
            and_self]

@[simp]
theorem IsDeadEnding.nat (n : ℕ) : IsDeadEnding (n : GameForm) := by
  match n with
  | .zero => exact IsDeadEnding.zero
  | .succ k =>
    unfold IsDeadEnding
    refine And.intro ?_ (GameForm.nat_forall_moves (IsDeadEnding.nat k))
    intro p h
    simp only [GameForm.succ_nat_end_right.mp h, IsDeadEnd.right_nat k.succ]

@[simp]
theorem IsDeadEnding.int (k : ℤ) : IsDeadEnding (k : GameForm) := by
  match k with
  | .ofNat n => exact IsDeadEnding.nat n
  | .negSucc n =>
    rw [Int.negSucc_eq, GameForm.intCast_neg, IsDeadEnding.neg_iff]
    norm_cast
    exact IsDeadEnding.nat (n + 1)

end GameForm
