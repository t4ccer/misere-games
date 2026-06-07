/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.PFree
public import CombinatorialGames.Misere.Universe

public section

namespace Form

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Form.Misere.Outcome

def IsDeadEnd (p : Player) (g : G) : Prop :=
  IsEnd p g ∧ (∀ gp ∈ moves (-p) g, IsDeadEnd p gp)
termination_by g
decreasing_by form_wf

theorem isDeadEnd_def (p : Player) (g : G) :
    IsDeadEnd p g ↔ IsEnd p g ∧ (∀ gp ∈ moves (-p) g, IsDeadEnd p gp) := by nth_rw 1 [IsDeadEnd]

theorem isEnd_of_isDeadEnd {g : G} {p : Player} (h1 : IsDeadEnd p g) : IsEnd p g := by
  unfold IsDeadEnd at h1
  exact h1.left

theorem IsDeadEnd.hereditary_def {g : G} {p : Player} (h1 : IsDeadEnd p g) :
    ∀ gp ∈ moves (-p) g, IsDeadEnd p gp := by
  unfold IsDeadEnd at h1
  exact h1.right

@[simp]
theorem not_mem_moves_of_isDeadEnd {g gp : G} {p : Player} (h1 : IsDeadEnd p g) : gp ∉ moves p g := by
  simp [isEnd_of_isDeadEnd h1]

theorem player_eq_neg_of_isDeadEnd_mem_moves {g gp : G} {p1 p2 : Player} (h1 : IsDeadEnd p1 g)
    (h2 : gp ∈ moves p2 g) : p2 = -p1 := by
  by_cases h3 : p2 = p1
  · rw [h3] at h2
    absurd h2
    simp only [h1, not_mem_moves_of_isDeadEnd, not_false_eq_true]
  · exact Player.ne_iff_eq_neg.mp h3

theorem isDeadEnd_of_mem_moves {g gp : G} {p1 p2 : Player} (h1 : IsDeadEnd p1 g) (h2 : gp ∈ moves p2 g)
      : IsDeadEnd p1 gp := by
  rw [player_eq_neg_of_isDeadEnd_mem_moves h1 h2] at h2
  exact IsDeadEnd.hereditary_def h1 gp h2

theorem isDeadEnd_isOption {p : Player} {g gp : G} (h1 : IsDeadEnd p g) (h2 : IsOption gp g) :
    gp ∈ moves (-p) g := isOption_not_mem h2 (not_mem_moves_of_isDeadEnd h1)

theorem isDeadEnd_of_isOption {g gp : G} {p : Player} (h1 : IsDeadEnd p g) (h2 : IsOption gp g) :
    IsDeadEnd p gp := isDeadEnd_of_mem_moves h1 (isDeadEnd_isOption h1 h2)

protected theorem IsDeadEnd.add {g h : G} {p : Player} (h1 : IsDeadEnd p g) (h2 : IsDeadEnd p h) :
    IsDeadEnd p (g + h) := by
  unfold IsDeadEnd
  simp only [moves_add, Set.mem_union, Set.mem_image]
  apply And.intro (IsEnd.add_iff.mpr ⟨isEnd_of_isDeadEnd h1, isEnd_of_isDeadEnd h2⟩)
  intro gp h3
  apply Or.elim h3 <;> intro ⟨gpp, h3, h4⟩ <;> rw [<-h4]
  · exact IsDeadEnd.add (isDeadEnd_of_mem_moves h1 h3) h2
  · exact IsDeadEnd.add h1 (isDeadEnd_of_mem_moves h2 h3)
termination_by (g, h)
decreasing_by all_goals form_wf

private protected theorem IsDeadEnd.neg {g : G} {p : Player} (h1 : IsDeadEnd p (-g)) : IsDeadEnd (-p) g := by
  have h0 := h1
  unfold IsDeadEnd at h1 ⊢
  have ⟨h3, h2⟩ := h1
  apply And.intro (IsEnd.neg_iff_neg.mp h3)
  rw [neg_neg]
  intro gp h4
  have h5 : IsDeadEnd p (-gp) := by
    rw [<-neg_neg g, moves_neg] at h4
    exact h2 (-gp) (Set.mem_neg.mp h4)
  exact IsDeadEnd.neg h5
termination_by g
decreasing_by form_wf

@[simp]
protected theorem IsDeadEnd.neg_iff {g : G} {p : Player} : IsDeadEnd p (-g) ↔ IsDeadEnd (-p) g := by
  constructor <;> intro h1
  · exact IsDeadEnd.neg h1
  · rw [<-neg_neg g] at h1
    rw [<-neg_neg p]
    exact IsDeadEnd.neg h1

@[simp]
theorem isDeadEnd_zero {p : Player} : IsDeadEnd p (0 : G) := by
  unfold IsDeadEnd
  simp only [isEnd_zero, moves_zero (G := G), Set.mem_empty_iff_false,
             IsEmpty.forall_iff, implies_true, and_self]

@[simp]
theorem isDeadEnd_right_natCast (n : ℕ) : IsDeadEnd .right (n : G) := by
  match n with
  | .zero => exact isDeadEnd_zero
  | .succ k => unfold IsDeadEnd; simp [isDeadEnd_right_natCast k]

@[simp]
theorem isDeadEnd_right_nonneg_intCast (k : ℤ) (h1 : k ≥ 0) : IsDeadEnd .right (k : G) := by
  rw [<-Int.toNat_of_nonneg h1]
  norm_cast
  simp only [isDeadEnd_right_natCast]

@[simp]
theorem isDeadEnd_left_nonpos_intCast (k : ℤ) (h1 : k ≤ 0) : IsDeadEnd .left (k : G) := by
  rw [<-Player.neg_right, <-IsDeadEnd.neg_iff]
  norm_cast
  exact isDeadEnd_right_nonneg_intCast (-k) (by omega)

theorem isPFree_of_isDeadEnd {g : G} {p : Player} (h1 : IsDeadEnd p g) : IsPFree g := by
  unfold IsPFree
  apply And.intro
  · have h2 := miserePlayerOutcome_eq_iff_winsGoingFirst.mpr (winsGoingFirst_of_isEnd (isEnd_of_isDeadEnd h1))
    cases p
    · cases h3 : MiserePlayerOutcome g .right <;> simp [MisereOutcome, Outcome.ofPlayers, h2, h3]
    · cases h3 : MiserePlayerOutcome g .left <;> simp [MisereOutcome, Outcome.ofPlayers, h2, h3]
  · intro p' gp h_gp
    exact isPFree_of_isDeadEnd (isDeadEnd_of_mem_moves h1 h_gp)
termination_by g
decreasing_by form_wf

@[expose] def IsDeadEnding (g : G) : Prop :=
  (∀ p, IsEnd p g → IsDeadEnd p g) ∧ (∀ p, ∀gp ∈ moves p g, IsDeadEnding gp)
termination_by g
decreasing_by form_wf

@[simp]
theorem isDeadEnd_of_isDeadEnding {g : G} {p : Player} (h1 : IsDeadEnding g) (h2 : IsEnd p g) :
    IsDeadEnd p g := by
  unfold IsDeadEnding at h1
  exact h1.left p h2

theorem isDeadEnding_of_mem_moves {g h : G} {p : Player} (h1 : IsDeadEnding g) (h2 : h ∈ moves p g) :
    IsDeadEnding h := by
  unfold IsDeadEnding at h1
  exact h1.right p h h2

theorem isDeadEnding_of_isOption {g g' : G} (h1 : IsDeadEnding g) (h2 : Moves.IsOption g' g)
    : IsDeadEnding g' := by
  rw [isOption_iff_mem_union, Set.mem_union] at h2
  apply Or.elim h2 <;> exact fun h2 => isDeadEnding_of_mem_moves h1 h2

end Form

namespace GameForm

open Form
open Form.Misere.Outcome

private theorem lemma3.aux {g : GameForm} {p : Player} (h1 : g ≠ 0) (h2 : IsDeadEnd p g) :
    MisereOutcome g = Outcome.ofPlayer p := by
  rw [misereOutcome_eq_player_iff]
  apply And.intro (winsGoingFirst_of_isEnd (isEnd_of_isDeadEnd h2))
  simp only [not_winsGoingFirst_iff, neg_neg, isEndLike_iff_isEnd]
  apply And.intro (zero_not_both_end h1 (isEnd_of_isDeadEnd h2))
  intro gr h4
  exact winsGoingFirst_of_isEnd (isEnd_of_isDeadEnd (isDeadEnd_of_mem_moves h2 h4))

theorem lemma3_L (g : GameForm) (h1 : g ≠ 0) (h2 : IsDeadEnd .left g) :
    MisereOutcome g = .L := lemma3.aux h1 h2

theorem lemma3_R (g : GameForm) (h1 : g ≠ 0) (h2 : IsDeadEnd .right g) :
    MisereOutcome g = .R := lemma3.aux h1 h2

@[simp]
theorem IsDeadEnding.add {g h : GameForm} (h1 : IsDeadEnding g) (h2 : IsDeadEnding h) :
    IsDeadEnding (g + h) := by
  unfold IsDeadEnding
  simp only [moves_add, Set.mem_union, Set.mem_image]
  constructor <;> intro p
  · intro h3
    have ⟨h4, h5⟩ := IsEnd.add_iff.mp h3
    exact IsDeadEnd.add (isDeadEnd_of_isDeadEnding h1 h4) (isDeadEnd_of_isDeadEnding h2 h5)
  · intro gp h3
    apply Or.elim h3 <;> intro ⟨g', h3, h4⟩ <;> rw [<-h4]
    · exact IsDeadEnding.add (isDeadEnding_of_mem_moves h1 h3) h2
    · exact IsDeadEnding.add h1 (isDeadEnding_of_mem_moves h2 h3)
termination_by (g, h)
decreasing_by all_goals form_wf

private protected theorem IsDeadEnding.neg {g : GameForm} (h1 : IsDeadEnding (-g)) : IsDeadEnding g := by
  unfold IsDeadEnding at h1 ⊢
  obtain ⟨h1, h2⟩ := h1
  apply And.intro
  · intro p h3
    rw [<-neg_neg p, <-IsEnd.neg_iff_neg] at h3
    have h4 := IsDeadEnd.neg_iff.mp (h1 (-p) h3)
    rwa [neg_neg] at h4
  · intro p gp h3
    have h4 := h2 (-p) (-gp) (by simp [h3])
    exact IsDeadEnding.neg h4
termination_by g
decreasing_by form_wf

instance : ClosedUnderNeg (IsDeadEnding (G := GameForm)) where
  neg_of {g} h := by
    rw [<-neg_neg g] at h
    exact IsDeadEnding.neg h

@[simp]
theorem isDeadEnding_zero : IsDeadEnding (0 : GameForm) := by
  unfold IsDeadEnding IsDeadEnd
  simp

@[simp]
theorem isDeadEnding_natCast (n : ℕ) : IsDeadEnding (n : GameForm) := by
  match n with
  | .zero => exact isDeadEnding_zero
  | .succ k =>
    unfold IsDeadEnding
    refine And.intro ?_ (nat_forall_moves (isDeadEnding_natCast k))
    intro p h
    simp only [succ_nat_end_right.mp h, isDeadEnd_right_natCast k.succ]

@[simp]
theorem isDeadEnding_intCast (k : ℤ) : IsDeadEnding (k : GameForm) := by
  match k with
  | .ofNat n => exact isDeadEnding_natCast n
  | .negSucc n =>
    rw [Int.negSucc_eq, Form.intCast_neg, ClosedUnderNeg.neg_iff (A := IsDeadEnding)]
    norm_cast
    exact isDeadEnding_natCast (n + 1)

@[simp]
theorem isDeadEnding_one : IsDeadEnding (1 : GameForm) := by
  rw [<-Form.intCast_one]
  exact isDeadEnding_intCast 1

structure ShortDeadEnding (g : GameForm) : Prop where
  short : IsShort g
  dead_ending : IsDeadEnding g

instance : Hereditary ShortDeadEnding where
  has_option h1 h2 :=
  { short := Short.isOption h1.short h2
  , dead_ending := isDeadEnding_of_isOption h1.dead_ending h2
  }

instance : ShortUniverse ShortDeadEnding where
  zero_mem :=
  { short := by
      rw [short_def]
      intro p
      simp
  , dead_ending := isDeadEnding_zero
  }
  isAmbient_of_mem h := h.short
  closed_sum _ _ h_g h_h :=
    { short := Short.add h_g.short h_h.short
    , dead_ending := IsDeadEnding.add h_g.dead_ending h_h.dead_ending
    }
  has_option := Hereditary.has_option
  neg_of h :=
    { short := ClosedUnderNeg.neg_iff.mpr h.short
    , dead_ending := ClosedUnderNeg.neg_iff.mpr h.dead_ending
    }
  closed_dicotic B C _ _ hB hC hBnon hCnon hAmbient :=
    { short := hAmbient
    , dead_ending := by
        unfold IsDeadEnding
        apply And.intro <;> intro p
        · cases p <;> intro h1 <;> simp only [isEnd_def, moves_ofSets, Player.cases] at h1
          · simp only [h1, Set.not_nonempty_empty] at hBnon
          · simp only [h1, Set.not_nonempty_empty] at hCnon
        · cases p <;> simp only [moves_ofSets, Player.cases] <;> intro gp hgp
          · exact (hB gp hgp).dead_ending
          · exact (hC gp hgp).dead_ending
    }

end GameForm
