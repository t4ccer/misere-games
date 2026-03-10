module

public import CombinatorialGames.Misere.PFree
public import CombinatorialGames.Misere.ShortUniverse

public section

namespace Form

universe u

variable {G : Type (u + 1)} [g_form : Form G]

open Form
open MisereForm
open GameForm.Misere.Outcome

def IsDeadEnd (p : Player) (g : G) : Prop :=
  IsEnd p g ∧ (∀ gp ∈ moves (-p) g, IsDeadEnd p gp)
termination_by g
decreasing_by form_wf

def IsDeadEnd.IsEnd {g : G} {p : Player} (h1 : IsDeadEnd p g) : IsEnd p g := by
  unfold IsDeadEnd at h1
  exact h1.left

def IsDeadEnd.hereditary_def {g : G} {p : Player} (h1 : IsDeadEnd p g) :
    ∀ gp ∈ moves (-p) g, IsDeadEnd p gp := by
  unfold IsDeadEnd at h1
  exact h1.right

@[simp]
theorem IsDeadEnd.not_mem_moves {g gp : G} {p : Player} (h1 : IsDeadEnd p g) : gp ∉ moves p g := by
  simp [h1.IsEnd]

theorem IsDeadEnd.mem_moves_player_eq_neg {g gp : G} {p1 p2 : Player} (h1 : IsDeadEnd p1 g)
    (h2 : gp ∈ moves p2 g) : p2 = -p1 := by
  by_cases h3 : p2 = p1
  · rw [h3] at h2
    absurd h2
    simp only [h1, IsDeadEnd.not_mem_moves, not_false_eq_true]
  · exact Player.ne_iff_eq_neg.mp h3

theorem IsDeadEnd.hereditary {g gp : G} {p1 p2 : Player} (h1 : IsDeadEnd p1 g) (h2 : gp ∈ moves p2 g)
      : IsDeadEnd p1 gp := by
  rw [IsDeadEnd.mem_moves_player_eq_neg h1 h2] at h2
  exact IsDeadEnd.hereditary_def h1 gp h2

protected theorem IsDeadEnd.add {g h : G} {p : Player} (h1 : IsDeadEnd p g) (h2 : IsDeadEnd p h) :
    IsDeadEnd p (g + h) := by
  unfold IsDeadEnd
  simp only [moves_add, Set.mem_union, Set.mem_image]
  apply And.intro (IsEnd.add_iff.mpr ⟨IsDeadEnd.IsEnd h1, IsDeadEnd.IsEnd h2⟩)
  intro gp h3
  apply Or.elim h3 <;> intro ⟨gpp, h3, h4⟩ <;> rw [<-h4]
  · exact IsDeadEnd.add (IsDeadEnd.hereditary h1 h3) h2
  · exact IsDeadEnd.add h1 (IsDeadEnd.hereditary h2 h3)
termination_by (g, h)
decreasing_by all_goals form_wf

private protected theorem IsDeadEnd.neg {g : G} {p : Player} (h1 : IsDeadEnd p (-g)) : IsDeadEnd (-p) g := by
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
protected theorem IsDeadEnd.neg_iff {g : G} {p : Player} : IsDeadEnd p (-g) ↔ IsDeadEnd (-p) g := by
  constructor <;> intro h1
  · exact IsDeadEnd.neg h1
  · rw [<-neg_neg g] at h1
    rw [<-neg_neg p]
    exact IsDeadEnd.neg h1

@[simp]
protected theorem IsDeadEnd.zero {p : Player} : IsDeadEnd p (0 : GameForm) := by
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

protected theorem IsDeadEnd.IsPFree {g : GameForm} {p : Player} (h1 : IsDeadEnd p g) : IsPFree g := by
  unfold IsPFree
  apply And.intro
  · have h2 := MiserePlayerOutcome_eq_iff_WinsGoingFirst.mpr (WinsGoingFirst_of_IsEnd (IsEnd h1))
    cases p
    · cases h3 : MiserePlayerOutcome g .right <;> simp [MisereOutcome, Outcome.ofPlayers, h2, h3]
    · cases h3 : MiserePlayerOutcome g .left <;> simp [MisereOutcome, Outcome.ofPlayers, h2, h3]
  · intro p' gp h_gp
    exact IsDeadEnd.IsPFree (IsDeadEnd.hereditary h1 h_gp)
termination_by g
decreasing_by form_wf

@[expose] def IsDeadEnding (g : G) : Prop :=
  (∀ p, IsEnd p g → IsDeadEnd p g) ∧ (∀ p, ∀gp ∈ moves p g, IsDeadEnding gp)
termination_by g
decreasing_by form_wf

@[simp]
theorem IsDeadEnding.IsDeadEnd {g : G} {p : Player} (h1 : IsDeadEnding g) (h2 : IsEnd p g) :
    IsDeadEnd p g := by
  unfold IsDeadEnding at h1
  exact h1.left p h2

@[simp]
theorem IsDeadEnding.hereditary {g h : G} {p : Player} (h1 : IsDeadEnding g) (h2 : h ∈ moves p g) :
    IsDeadEnding h := by
  unfold IsDeadEnding at h1
  exact h1.right p h h2

@[simp]
theorem IsDeadEnding.IsOption {g g' : G} (h1 : IsDeadEnding g) (h2 : Moves.IsOption g' g)
    : IsDeadEnding g' := by
  rw [isOption_iff_mem_union, Set.mem_union] at h2
  apply Or.elim h2 <;> exact fun h2 => hereditary h1 h2

end Form

namespace GameForm

open GameForm.Misere.Outcome
open Form
open Form.Misere.Outcome
open MisereForm

private theorem lemma3.aux {g : GameForm} {p : Player} (h1 : g ≠ 0) (h2 : IsDeadEnd p g) :
    MisereForm.MisereOutcome g = Outcome.ofPlayer p := by
  rw [MisereOutcome_eq_player_iff]
  apply And.intro (WinsGoingFirst_of_IsEnd (IsDeadEnd.IsEnd h2))
  simp only [not_WinsGoingFirst, neg_neg, GameForm.IsEndLike_iff]
  apply And.intro (zero_not_both_end h1 (IsDeadEnd.IsEnd h2))
  intro gr h4
  exact WinsGoingFirst_of_IsEnd (IsDeadEnd.IsEnd (IsDeadEnd.hereditary h2 h4))

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
    · exact IsDeadEnding.add (IsDeadEnding.hereditary h1 h3) h2
    · exact IsDeadEnding.add h1 (IsDeadEnding.hereditary h2 h3)
termination_by (g, h)
decreasing_by all_goals form_wf

private protected theorem IsDeadEnding.neg {g : GameForm} (h1 : IsDeadEnding (-g)) : IsDeadEnding g := by
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

instance : ClosedUnderNeg IsDeadEnding where
  neg_of {g} h := by
    rw [<-neg_neg g] at h
    exact IsDeadEnding.neg h

@[simp]
protected theorem IsDeadEnding.zero : IsDeadEnding (0 : GameForm) := by
  unfold IsDeadEnding IsDeadEnd
  simp only [IsEnd_zero, moves_zero, Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true,
            and_self]

@[simp]
protected theorem IsDeadEnding.nat (n : ℕ) : IsDeadEnding (n : GameForm) := by
  match n with
  | .zero => exact IsDeadEnding.zero
  | .succ k =>
    unfold IsDeadEnding
    refine And.intro ?_ (GameForm.nat_forall_moves (IsDeadEnding.nat k))
    intro p h
    simp only [GameForm.succ_nat_end_right.mp h, IsDeadEnd.right_nat k.succ]

@[simp]
protected theorem IsDeadEnding.int (k : ℤ) : IsDeadEnding (k : GameForm) := by
  match k with
  | .ofNat n => exact IsDeadEnding.nat n
  | .negSucc n =>
    rw [Int.negSucc_eq, GameForm.intCast_neg, ClosedUnderNeg.neg_iff (A := IsDeadEnding)]
    norm_cast
    exact IsDeadEnding.nat (n + 1)

@[simp]
protected theorem IsDeadEnding.one : IsDeadEnding (1 : GameForm) := by
  rw [<-GameForm.intCast_one]
  exact IsDeadEnding.int 1

structure ShortDeadEnding (g : GameForm) : Prop where
  short : Short g
  dead_ending : IsDeadEnding g

instance : ShortUniverse ShortDeadEnding where
  closed_sum _ _ h_g h_h :=
  { short := Short.add' h_g.short h_h.short
  , dead_ending := IsDeadEnding.add h_g.dead_ending h_h.dead_ending
  }
  closed_follower g h1 g' h2 :=
  { short := by
      have := h1.short
      exact Short.isOption h2
  , dead_ending := IsDeadEnding.IsOption h1.dead_ending h2
  }
  neg_of h :=
  { short := ClosedUnderNeg.neg_iff.mpr h.short
  , dead_ending := ClosedUnderNeg.neg_iff.mpr h.dead_ending
  }
  closed_dicotic_short B C b c hb hb' hc hc' _ _ :=
  { short := by
      rw [short_def]
      intro p
      apply And.intro (by cases p <;> simp only [moves_ofSets, Player.cases, hb, hc])
      intro y
      cases p <;> simp only [moves_ofSets, Player.cases] <;> intro hy
      · exact (b y hy).short
      · exact (c y hy).short
  , dead_ending := by
      unfold IsDeadEnding
      apply And.intro <;> intro p
      · cases p <;> intro h1 <;> simp only [IsEnd_def, moves_ofSets, Player.cases] at h1
        · simp only [h1, Set.not_nonempty_empty] at hb'
        · simp only [h1, Set.not_nonempty_empty] at hc'
      · cases p <;> simp only [moves_ofSets, Player.cases] <;> intro gp hgp
        · exact (b gp hgp).dead_ending
        · exact (c gp hgp).dead_ending
  }
  short_only _ h  := h.short

end GameForm
