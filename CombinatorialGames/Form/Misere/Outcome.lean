/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Form.ClosedUnderNeg
public import CombinatorialGames.Form.Birthday

public section

namespace Form.Misere.Outcome

open Form

universe u

variable {G : Type (u + 1)} [Form G]

def WinsGoingFirst (p : Player) (g : G) : Prop := IsEndLike p g ∨ (∃ g', ∃ (_ : g' ∈ moves p g), ¬WinsGoingFirst (-p) g')
  termination_by g
  decreasing_by exact Moves.Subposition.of_mem_moves (by assumption)

theorem winsGoingFirst_iff (g : G) (p : Player)
    : WinsGoingFirst p g ↔ IsEndLike p g ∨ (∃ g' ∈ moves p g, ¬WinsGoingFirst (-p) g') := by
  apply Iff.intro <;> intro h1
  · unfold WinsGoingFirst at h1
    obtain h1 | ⟨g', h2, h3⟩ := h1
    · exact Or.inl h1
    · apply Or.inr
      use g'
  · unfold WinsGoingFirst
    obtain h1 | ⟨g', h2⟩ := h1
    · exact Or.inl h1
    · apply Or.inr
      use g'

@[simp]
theorem winsGoingFirst_of_isEndLike {g : G} {p : Player} (h1 : IsEndLike p g) : WinsGoingFirst p g :=
  (winsGoingFirst_iff g p).mpr (Or.inl h1)

@[simp]
theorem winsGoingFirst_of_isEnd {g : G} {p : Player} (h1 : IsEnd p g) : WinsGoingFirst p g :=
  (winsGoingFirst_iff g p).mpr (Or.inl (isEndLike_of_isEnd h1))

theorem winsGoingFirst_of_moves {g : G} {p : Player}
    (h1 : ∃ g' ∈ Form.moves p g, ¬WinsGoingFirst (-p) g')
    : WinsGoingFirst p g := by
  rw [winsGoingFirst_iff]
  exact Or.inr h1

theorem winsGoingFirst_neg_iff (g : G) (p : Player) : (WinsGoingFirst p (-g)) ↔ (WinsGoingFirst (-p) g) := by
  constructor
    <;> intro h1
    <;> rw [winsGoingFirst_iff] at h1
    <;> apply Or.elim h1
    <;> intro h1
  · refine winsGoingFirst_of_isEndLike ?_
    rwa [<-IsEndLike.neg_iff_neg]
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [(winsGoingFirst_iff g (-p))]
    refine Or.inr ?_
    use -gp
    constructor
    · rwa [moves_neg, Set.mem_neg] at h1
    · rwa [neg_neg, winsGoingFirst_neg_iff]
  · refine winsGoingFirst_of_isEndLike ?_
    rwa [IsEndLike.neg_iff_neg]
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [neg_neg] at h2
    rw [winsGoingFirst_iff]
    apply Or.inr
    use -gp
    constructor
    · rwa [moves_neg, Set.mem_neg, neg_neg]
    · rwa [winsGoingFirst_neg_iff, neg_neg]
termination_by birthday g
decreasing_by all_goals gameform_birthday

theorem not_winsGoingFirst_iff {g : G} {p : Player}
    : ¬WinsGoingFirst p g ↔ (¬Form.IsEndLike p g ∧ (∀ g' ∈ Form.moves p g, WinsGoingFirst (-p) g')) := by
  rw [winsGoingFirst_iff]
  simp only [not_or, not_exists, not_and, not_not]

@[simp]
theorem winsGoingFirst_zero (p : Player) : WinsGoingFirst p (0 : G) :=
  winsGoingFirst_of_isEnd isEnd_zero

open scoped Classical in
@[expose] noncomputable def MiserePlayerOutcome : G → Player → Player :=
  fun g p => if WinsGoingFirst p g then p else -p

open scoped Classical in
@[expose] noncomputable def MisereOutcome : G → Outcome :=
  fun g => Outcome.ofPlayers (MiserePlayerOutcome g .left) (MiserePlayerOutcome g .right)

@[simp]
theorem miserePlayerOutcome_eq_iff_winsGoingFirst {g : G} {p : Player}
    : (MiserePlayerOutcome g p = p) ↔ WinsGoingFirst p g := by
  apply Iff.intro <;> intro h1
  · simp only [MiserePlayerOutcome] at h1
    by_cases h2 : WinsGoingFirst p g
    · exact h2
    · simp [h2] at h1
      cases p <;> simp at h1
  · simp only [MiserePlayerOutcome, h1, ↓reduceIte]

theorem misereOutcome_L_iff_miserePlayerOutcome {g : G}
    : (MisereOutcome g = .L) ↔ ((MiserePlayerOutcome g .left = .left) ∧ (MiserePlayerOutcome g .right = .left)) := by
  simp [MiserePlayerOutcome, MisereOutcome, Outcome.ofPlayers]
  by_cases h1 : WinsGoingFirst Player.left g
  <;> by_cases h2 : WinsGoingFirst Player.right g
  <;> simp [h1, h2]

theorem misereOutcome_N_iff_miserePlayerOutcome {g : G}
    : (MisereOutcome g = .N) ↔ ((MiserePlayerOutcome g .left = .left) ∧ (MiserePlayerOutcome g .right = .right)) := by
  simp [MiserePlayerOutcome, MisereOutcome, Outcome.ofPlayers]
  by_cases h1 : WinsGoingFirst Player.left g
  <;> by_cases h2 : WinsGoingFirst Player.right g
  <;> simp [h1, h2]

theorem misereOutcome_P_iff_miserePlayerOutcome {g : G}
    : (MisereOutcome g = .P) ↔ ((MiserePlayerOutcome g .left = .right) ∧ (MiserePlayerOutcome g .right = .left)) := by
  simp [MiserePlayerOutcome, MisereOutcome, Outcome.ofPlayers]
  by_cases h1 : WinsGoingFirst Player.left g
  <;> by_cases h2 : WinsGoingFirst Player.right g
  <;> simp [h1, h2]

theorem misereOutcome_R_iff_miserePlayerOutcome {g : G}
    : (MisereOutcome g = .R) ↔ ((MiserePlayerOutcome g .left = .right) ∧ (MiserePlayerOutcome g .right = .right)) := by
  simp [MiserePlayerOutcome, MisereOutcome, Outcome.ofPlayers]
  by_cases h1 : WinsGoingFirst Player.left g
  <;> by_cases h2 : WinsGoingFirst Player.right g
  <;> simp [h1, h2]

@[simp]
theorem minsGoingFirst_left_of_misereOutcome_L {g : G}
    (h1 : MisereOutcome g = .L) : WinsGoingFirst .left g := by
  rw [misereOutcome_L_iff_miserePlayerOutcome, miserePlayerOutcome_eq_iff_winsGoingFirst] at h1
  exact h1.left

@[simp]
theorem winsGoingFirst_right_of_misereOutcome_R {g : G}
    (h1 : MisereOutcome g = .R) : WinsGoingFirst .right g := by
  rw [misereOutcome_R_iff_miserePlayerOutcome, miserePlayerOutcome_eq_iff_winsGoingFirst] at h1
  exact h1.right

private theorem conjugate_misereOutcome_of_ofPlayers_neg (g : G) :
    Outcome.ofPlayers
      (-(MiserePlayerOutcome g .right))
      (-(MiserePlayerOutcome g .left))
    = Outcome.Conjugate (MisereOutcome g) := by
  cases h1 : MiserePlayerOutcome g .right
  <;> cases h2 : MiserePlayerOutcome g .left
  all_goals simp only [h1, h2, Outcome.Conjugate, Outcome.ofPlayers, MisereOutcome]

@[simp]
theorem miserePlayerOutcome_neg_player_neg (g : G) (p : Player) :
    MiserePlayerOutcome (-g) p = -(MiserePlayerOutcome g (-p)) := by
  unfold MiserePlayerOutcome
  rw [winsGoingFirst_neg_iff g p, neg_neg]
  cases p
  · by_cases h1 : WinsGoingFirst .right g <;> simp [h1]
  · by_cases h1 : WinsGoingFirst .left g <;> simp [h1]

@[simp]
theorem misereOutcome_conjugate_neg (g : G) :
    (MisereOutcome g).Conjugate = MisereOutcome (-g) := by
  unfold Outcome.Conjugate
  cases h1 : MisereOutcome g
  all_goals
  · unfold MisereOutcome
    rw [miserePlayerOutcome_neg_player_neg, Player.neg_left,
        miserePlayerOutcome_neg_player_neg, Player.neg_right,
        conjugate_misereOutcome_of_ofPlayers_neg g, h1]
    rfl

theorem misereOutcome_ge_P_of_not_winsGoingFirst_right {g : G} (h1 : ¬WinsGoingFirst .right g) :
    MisereOutcome g ≥ Outcome.P := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
  by_cases h2 : WinsGoingFirst .left g
  all_goals simp only [h1, h2, reduceIte, ge_iff_le, le_refl, Outcome.L_ge]

theorem misereOutcome_le_N_of_winsGoingFirst_right {g : G} (h1 : WinsGoingFirst .right g) :
    MisereOutcome g ≤ Outcome.N := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
  by_cases h2 : WinsGoingFirst .left g <;> simp [h1, h2]

theorem not_winsGoingFirst_of_misereOutcome_P {g : G} {p : Player}
    (h1 : MisereOutcome g = Outcome.P) : ¬WinsGoingFirst p g := by
  intro h2
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h1
  by_cases h3 : WinsGoingFirst .left g
  <;> by_cases h4 : WinsGoingFirst .right g
  <;> simp only [h3, h4, reduceIte, reduceCtorEq, Player.neg_left, Player.neg_right] at h1
  cases p
  · exact h3 h2
  · exact h4 h2

theorem misereOutcome_P_of_miserePlayerOutcome_neg {g : G} (h1 : ∀ p, MiserePlayerOutcome g p = -p) :
    MisereOutcome g = Outcome.P := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [h1 .left, h1 .right]

@[simp]
theorem misereOutcome_eq_player_iff (g : G) (p : Player) :
    (MisereOutcome g = Outcome.ofPlayer p) ↔ (WinsGoingFirst p g ∧ ¬WinsGoingFirst (-p) g) := by
  constructor <;> intro h1
  · unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h1
    by_cases h2 : WinsGoingFirst .left g
      <;> by_cases h3 : WinsGoingFirst .right g
      <;> cases p
      <;> simp only [h2, h3, Outcome.ofPlayer, Player.neg_left, Player.neg_right, reduceIte,
                     reduceCtorEq] at h1
    · exact And.intro h2 h3
    · exact And.intro h3 h2
  · unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
    cases p
    <;> simp only [Player.neg_left, Player.neg_right] at h1
    <;> simp only [h1, reduceIte, Player.neg_right, Outcome.ofPlayer]

theorem misereOutcome_L_iff_winsGoingFirst {g : G} :
    (MisereOutcome g = .L) ↔ (WinsGoingFirst .left g ∧ ¬WinsGoingFirst .right g) := by
  have h1 : Outcome.L = Outcome.ofPlayer .left := by rfl
  have h2 : Player.right = -Player.left := rfl
  rw [h1, h2]
  exact misereOutcome_eq_player_iff g Player.left

theorem misereOutcome_R_iff_winsGoingFirst {g : G} :
    (MisereOutcome g = .R) ↔ (WinsGoingFirst .right g ∧ ¬WinsGoingFirst .left g) := by
  have h1 : Outcome.R = Outcome.ofPlayer .right := by rfl
  have h2 : Player.left = -Player.right := by rfl
  rw [h1, h2]
  exact misereOutcome_eq_player_iff g Player.right

theorem misereOutcome_P_iff_winsGoingFirst' {g : G} {p : Player} :
    (MisereOutcome g = .P) ↔ (¬WinsGoingFirst p g ∧ ¬WinsGoingFirst (-p) g) := by
  constructor
  · intro h1
    exact ⟨not_winsGoingFirst_of_misereOutcome_P h1, not_winsGoingFirst_of_misereOutcome_P h1⟩
  · intro ⟨h1, h2⟩
    unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
    cases p
    all_goals
    · simp only [Player.neg_right, Player.neg_left] at h2
      simp only [h1, h2, Player.neg_left, Player.neg_right, Player.neg_right, reduceIte]

theorem misereOutcome_P_iff_winsGoingFirst {g : G} :
    (MisereOutcome g = .P) ↔ (¬WinsGoingFirst .right g ∧ ¬WinsGoingFirst .left g) := by
  rw [<-Player.neg_right]
  exact misereOutcome_P_iff_winsGoingFirst'

theorem misereOutcome_N_iff_winsGoingFirst {g : G} :
    (MisereOutcome g = .N) ↔ (WinsGoingFirst .left g ∧ WinsGoingFirst .right g) := by
  simp only [← miserePlayerOutcome_eq_iff_winsGoingFirst]
  cases h_left : MiserePlayerOutcome g .left
  <;> cases h_right : MiserePlayerOutcome g .right
  <;> simp [MisereOutcome, Outcome.ofPlayers, h_left, h_right]

@[simp]
theorem miserePlayerOutcome_zero (p : Player) : MiserePlayerOutcome (0 : G) p = p := by
  unfold MiserePlayerOutcome
  simp only [winsGoingFirst_zero, ↓reduceIte]

@[simp]
theorem misereOutcome_zero_N : MisereOutcome (0 : G) = .N := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [miserePlayerOutcome_zero]

@[simp]
theorem misereOutcome_neg_R_iff_misereOutcome {g : G}
    : (MisereOutcome (-g) = .R) ↔ (MisereOutcome g = .L) := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [miserePlayerOutcome_neg_player_neg, Player.neg_left, Player.neg_right]
  cases MiserePlayerOutcome g Player.right
  <;> cases MiserePlayerOutcome g Player.left
  <;> simp

@[simp]
theorem misereOutcome_neg_L_iff_misereOutcome {g : G}
    : (MisereOutcome (-g) = .L) ↔ (MisereOutcome g = .R) := by
  rw [<-neg_neg g, misereOutcome_neg_R_iff_misereOutcome, neg_neg]

@[simp]
theorem misereOutcome_neg_N_iff_misereOutcome {g : G}
    : (MisereOutcome (-g) = .N) ↔ (MisereOutcome g = .N) := by
  rw [← misereOutcome_conjugate_neg]
  cases MisereOutcome g <;> simp [Outcome.Conjugate]

theorem winsGoingFirst_left_of_move_misereOutcome_P {g gl : G} (h1 : gl ∈ moves .left g)
    (h2 : MisereOutcome gl = Outcome.P) : WinsGoingFirst .left g := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h2
  by_cases h3 : WinsGoingFirst .left gl
    <;> by_cases h4 : WinsGoingFirst .right gl
    <;> simp only [h3, h4, reduceIte, reduceCtorEq] at h2
  apply winsGoingFirst_of_moves
  simp only [Player.neg_left]
  use gl

theorem winsGoingFirst_add_of_isEndLike {g h : G} {p : Player} (h1 : IsEndLike p g)
    (h2 : IsEndLike p h) : WinsGoingFirst p (g + h) :=
  winsGoingFirst_of_isEndLike (IsEndLike.add_iff.mpr ⟨h1, h2⟩)

theorem winsGoingFirst_add_of_isEnd {g h : G} {p : Player} (h1 : IsEnd p g)
    (h2 : IsEnd p h) : WinsGoingFirst p (g + h) :=
  winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨h1, h2⟩)

theorem miserePlayerOutcome_of_leftMoves {g gl : G} (h1 : gl ∈ moves .left g)
    (h2 : MiserePlayerOutcome gl .right = .left) : MiserePlayerOutcome g .left = .left := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst, winsGoingFirst_iff]
  apply Or.inr
  use gl
  apply And.intro h1
  simp only [Player.neg_left, Player.right_le, Player.le_right_eq]
  unfold MiserePlayerOutcome at h2
  simp only [Player.le_left, Player.neg_right, Player.le_left_eq, ite_eq_right_iff,
             reduceCtorEq, imp_false] at h2
  exact h2

theorem miserePlayerOutcome_of_rightMoves {g gr : G} (h1 : gr ∈ moves .right g)
    (h2 : MiserePlayerOutcome gr .left = .right) : MiserePlayerOutcome g .right = .right := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst, winsGoingFirst_iff]
  refine Or.inr ⟨gr, h1, ?_⟩
  intro h3
  have h4 : MiserePlayerOutcome gr .left = .left := by
    rwa [miserePlayerOutcome_eq_iff_winsGoingFirst]
  rw [h4] at h2
  cases h2

-- TODO: Golf
theorem misereOutcome_ge_iff_miserePlayerOutcome_ge {g h : G}
    : MisereOutcome g ≥ MisereOutcome h ↔ (∀ p, MiserePlayerOutcome g p ≥ MiserePlayerOutcome h p) := by
  apply Iff.intro <;> intro h1
  · intro p; cases p
    · simp [MisereOutcome, Outcome.ofPlayers] at h1
      cases h4 : MiserePlayerOutcome g Player.left
      <;> cases h5 : MiserePlayerOutcome g Player.right
      <;> cases h6 : MiserePlayerOutcome h Player.left
      <;> cases h7 : MiserePlayerOutcome h Player.right
      <;> simp [h4, h5, h6, h7] at h1
      <;> try decide
      · absurd h1
        decide
      · absurd h1
        decide
    · simp [MisereOutcome, Outcome.ofPlayers] at h1
      cases h4 : MiserePlayerOutcome g Player.left
      <;> cases h5 : MiserePlayerOutcome g Player.right
      <;> cases h6 : MiserePlayerOutcome h Player.left
      <;> cases h7 : MiserePlayerOutcome h Player.right
      <;> simp [h4, h5, h6, h7] at h1
      <;> try decide
      · absurd h1
        decide
      · absurd h1
        decide
  · have h2 := h1 .left
    have h3 := h1 .right
    cases h4 : MiserePlayerOutcome g Player.left
    <;> cases h5 : MiserePlayerOutcome g Player.right
    <;> cases h6 : MiserePlayerOutcome h Player.left
    <;> cases h7 : MiserePlayerOutcome h Player.right
    <;> simp [MisereOutcome, Outcome.ofPlayers, h4, h5, h6, h7] at ⊢ h2 h3
    · exact (Player.left_le_right h3).elim
    · exact (Player.left_le_right h3).elim
    · exact (Player.left_le_right h2).elim
    · exact (Player.left_le_right h2).elim
    · exact (Player.left_le_right h2).elim
    · exact (Player.left_le_right h2).elim
    · exact (Player.left_le_right h3).elim

/--
Misere equality modulo set `A`
-/
@[expose] def MisereEQ (A : G → Prop) (g h : G) : Prop :=
  ∀ (x : G), A x → MisereOutcome (g + x) = MisereOutcome (h + x)

@[inherit_doc MisereEQ]
syntax (name := misereEQ) term:51 " =m " term:max term:51 : term

macro_rules (kind := misereEQ)
  | `($x =m $u $y) => `(MisereEQ $u $x $y)

recommended_spelling "misereEQ" for "=m" in [MisereEQ, misereEQ]

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab MisereEQ]
meta def delab_misereEQ : Delab := do
  let y ← withAppArg delab
  let x ← withAppFn do withAppArg delab
  let u ← withAppFn do withAppFn do withAppArg delab
  `($x =m $u $y)

theorem MisereEQ.symm {A : G → Prop} {g h : G} (h1 : g =m A h) : h =m A g := by
  intro x h2
  have h3 := h1 x h2
  exact Eq.symm h3

theorem MisereEQ.trans {A : G → Prop} {g h k : G} (h1 : g =m A h) (h2 : h =m A k) :
    g =m A k := by
  unfold MisereEQ at *
  intro x h3
  exact cast (congrArg (Eq (MisereOutcome (g + x))) (h2 x h3)) (h1 x h3)

/--
Misere inequality modulo set `A`
-/
@[expose] def MisereGE (A : G → Prop) (g h : G) : Prop :=
  ∀ x, (A x → MisereOutcome (g + x) ≥ MisereOutcome (h + x))

@[inherit_doc MisereGE]
syntax (name := misereGE) term:51 " ≥m " term:max term:51 : term

macro_rules (kind := misereGE)
  | `($x ≥m $u $y) => `(MisereGE $u $x $y)

recommended_spelling "misereGE" for "≥m" in [MisereGE, misereGE]

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab MisereGE]
meta def delab_misereGE : Delab := do
  let y ← withAppArg delab
  let x ← withAppFn do withAppArg delab
  let u ← withAppFn do withAppFn do withAppArg delab
  `($x ≥m $u $y)

theorem MisereEq.of_antisymm {A : G → Prop} {g h : G} (h1 : g ≥m A h) (h2 : h ≥m A g) :
    g =m A h := fun x h3 =>
  PartialOrder.le_antisymm (MisereOutcome (g + x)) (MisereOutcome (h + x)) (h2 x h3) (h1 x h3)

theorem MisereGE.trans {A : G → Prop} {g h k : G} (h1 : g ≥m A h) (h2 : h ≥m A k) :
    g ≥m A k := by
  unfold MisereGE at *
  intro x h3
  exact le_trans (h2 x h3) (h1 x h3)

theorem misereGE_rw_left {A : G → Prop} {a b c : G} (h2 : b =m A c) (h1 : b ≥m A a) : c ≥m A a := by
  unfold MisereGE at h1 ⊢
  unfold MisereEQ at h2
  intro x hx
  rw [<-h2 x hx]
  exact h1 x hx

theorem misereGE_rw_right {A : G → Prop} {a b c : G} (h2 : b =m A c) (h1 : a ≥m A c) : a ≥m A b := by
  unfold MisereGE at h1 ⊢
  unfold MisereEQ at h2
  intro x hx
  rw [h2 x hx]
  exact h1 x hx

theorem misereGE_of_subset (U : G → Prop) {V : G → Prop}
    (h_v_subset_u : ∀g, V g → U g) (g h : G) (h2 : g ≥m U h) : g ≥m V h := by
  unfold MisereGE at h2 ⊢
  intro x hv
  exact h2 x (h_v_subset_u x hv)

@[simp]
theorem MisereGE.refl {A : G → Prop} (g : G) : g ≥m A g := by
  unfold MisereGE
  intro x h3
  exact le_refl MisereOutcome (g + x)

theorem not_misereEQ_of_not_misereGE {A : G → Prop} {g h : G} (h1 : ¬(g ≥m A h)) :
    ¬(g =m A h) := by
  simp only [MisereGE, ge_iff_le, not_forall] at h1
  obtain ⟨x, ⟨h1, h2⟩⟩ := h1
  simp only [MisereEQ, not_forall]
  use x
  use h1
  exact Ne.symm (ne_of_not_le h2)

private theorem ClosedUnderNeg.not_ge_neg_iff.aux {A : G → Prop} [ClosedUnderNeg A]
    {g h : G} (h1 : g ≥m A h) : (-h) ≥m A (-g) := by
  unfold MisereGE at *
  intro x h0
  have h2 := h1 (-x) (ClosedUnderNeg.neg_iff.mpr h0)
  have h4 : MisereOutcome (-h + x) = (MisereOutcome (-h + x)).Conjugate.Conjugate :=
    Eq.symm Outcome.conjugate_conjugate_eq_self
  have h5 : (MisereOutcome (-h + x)).Conjugate.Conjugate = (MisereOutcome (h + (-x))).Conjugate :=
    by simp only [misereOutcome_conjugate_neg, neg_add_rev, neg_neg, add_comm]
  rw [h4, h5]
  have h6 : (MisereOutcome (g + (-x))).Conjugate = MisereOutcome (-g + x) := by
    simp only [misereOutcome_conjugate_neg, neg_add_rev, neg_neg, add_comm]
  rw [<-h6]
  apply Outcome.outcome_ge_conjugate_le
  exact h2

@[simp]
theorem ClosedUnderNeg.neg_ge_neg_iff {A : G → Prop} [ClosedUnderNeg A]
    (g h : G) : (-h) ≥m A (-g) ↔ g ≥m A h := by
  constructor <;> intro h1
  · have h2 := not_ge_neg_iff.aux h1
    simp only [neg_neg] at h2
    exact h2
  · exact not_ge_neg_iff.aux h1

@[simp]
theorem one_misereOutcome_R : MisereOutcome (1 : G) = .R := by
  simp only [misereOutcome_R_iff_winsGoingFirst]
  constructor
  · exact winsGoingFirst_of_isEndLike one_isEndLike_right
  · rw [not_winsGoingFirst_iff]
    simp [isEnd_def]

@[simp]
theorem pos_nat_misereOutcome_R {n : ℕ} (h1 : n > 0) : MisereOutcome (n : G) = .R := by
  induction n, h1 using Nat.le_induction with
  | base => simp
  | succ k h2 ih =>
    rw [Nat.cast_add, Nat.cast_one, misereOutcome_R_iff_winsGoingFirst]
    constructor
    · exact winsGoingFirst_of_isEnd (natCast_isEnd_right (k + 1))
    · rw [not_winsGoingFirst_iff]
      simp [isEnd_def]

@[simp]
theorem pos_int_misereOutcome_R {n : ℤ} (h1 : n > 0) : MisereOutcome (n : G) = .R := by
  rw [<-Int.toNat_of_nonneg (Int.le_of_lt h1)]
  exact pos_nat_misereOutcome_R (Int.pos_iff_toNat_pos.mp h1)

@[simp]
theorem neg_int_misereOutcome_L {n : ℤ} (h1 : n < 0) : MisereOutcome (n : G) = .L := by
  have h2 := pos_int_misereOutcome_R (G := G) (Int.neg_pos.mpr h1)
  rwa [Form.intCast_neg, misereOutcome_neg_R_iff_misereOutcome] at h2

@[simp]
theorem zero_int_misereOutcome_N {n : ℤ} (h1 : n = 0) : MisereOutcome (n : G) = .N := by
  rw [h1, Form.intCast_ofNat, Nat.cast_zero, misereOutcome_zero_N]

end Form.Misere.Outcome
