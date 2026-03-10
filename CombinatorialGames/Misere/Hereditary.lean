module

public import CombinatorialGames.GameForm.Misere.Outcome

public section

universe u

open Form
open Form.Misere.Outcome
open GameForm.Misere.Outcome
open GameForm
open MisereForm

namespace GameForm

@[expose] def Maintenance (U : GameForm → Prop) (g h : GameForm) (p : Player) : Prop :=
  match p with
  | .right => ∀ gr ∈ moves .right g,
      (∃ hr ∈ moves .right h, gr ≥m U hr) ∨
      (∃ grl ∈ moves .left gr, grl ≥m U h)
  | .left => ∀ hl ∈ moves .left h,
      (∃ gl ∈ moves .left g, gl ≥m U hl) ∨
      (∃ hlr ∈ moves .right hl, g ≥m U hlr)

@[expose] def Strong (U : GameForm → Prop) (g : GameForm) (p : Player) : Prop :=
  ∀ x, U x → IsEnd p x → WinsGoingFirst p (g + x)

@[expose] def Proviso (U : GameForm → Prop) (g h : GameForm) (p : Player) : Prop :=
  IsEnd p g → Strong U h p

class Hereditary (A : GameForm → Prop) where
  has_option {g g' : GameForm} (h1 : A g) (h2 : Moves.IsOption g' g) : A g'

private theorem auxCases {h x : GameForm} {p : Player} (h1 : MiserePlayerOutcome (h + x) p = p)
    : (∃ xl ∈ moves p x, MiserePlayerOutcome (h + xl) (-p) = p)
    ∨ (∃ hl ∈ moves p h, MiserePlayerOutcome (hl + x) (-p) = p)
    ∨ (IsEnd p (h + x)) := by
  apply Or.elim ((WinsGoingFirst_iff _ _).mp (MiserePlayerOutcome_eq_iff_WinsGoingFirst.mp h1))
  · intro h1
    exact (Or.inr (Or.inr h1))
  · intro ⟨hxl, h1, h2⟩
    simp at h1 h2
    apply Or.elim h1
    · intro ⟨hl, h3, h4⟩
      refine Or.inr (Or.inl ?_)
      use hl
      apply And.intro h3
      rw [h4]
      simp [MiserePlayerOutcome, h2]
    · intro ⟨xl, h3, h4⟩
      apply Or.inl
      use xl
      apply And.intro h3
      rw [h4]
      simp [MiserePlayerOutcome, h2]

mutual

-- TODO: Combine proofs

private theorem auxR (A : GameForm → Prop) [Hereditary A]
    {g h x : GameForm}
    (hx : A x)
    (h2 : Maintenance A g h .right) (h3 : Maintenance A g h .left)
    (h4 : Proviso A g h .right) (h5 : Proviso A h g .left)
    (h6 : MiserePlayerOutcome (g + x) .right = .right)
    : MiserePlayerOutcome (h + x) .right = .right := by
  -- We must be in one of three cases:
  apply Or.elim3 (auxCases h6)
  · -- 1. o^L(G + X^R) = R for some X^R.
    intro ⟨xr, h7, h8⟩
    rw [Player.neg_right] at h8
    -- By induction on X^R, since A is hereditary, we have o^L(H + X^R) = R.
    have h9 : MiserePlayerOutcome (g + xr) .left ≥ MiserePlayerOutcome (h + xr) .left := by
      exact MisereOutcome_ge_iff_MiserePlayerOutcome_ge.mp
        (aux A h2 h3 h4 h5
          (Hereditary.has_option hx (IsOption.of_mem_moves h7))) .left
    have h10 : MiserePlayerOutcome (h + xr) .left = .right := by
      have h11 : MiserePlayerOutcome (h + xr) .left ≤ .right := by
        simpa [h8] using h9
      exact Player.le_right_eq _ h11
    -- and hence oR(H + X) = R.
    exact MiserePlayerOutcome_moves_right (add_left_mem_moves_add h7 h) h10
  · -- 2. o^L(G^R + X) = R for some G^R.
    intro ⟨gr, h7, h8⟩
    rw [Player.neg_right] at h8
    -- By hypothesis,
    apply Or.elim (h2 gr h7)
    · -- either there exists some H^R with G^R ≥A H^R,
      intro ⟨hr, h9, h10⟩
      -- In the first case, we have immediately that o^L(G^R + X) ≥ o^L(H^R + X),
      have h11 : MiserePlayerOutcome (gr + x) .left ≥ MiserePlayerOutcome (hr + x) .left := by
        exact MisereOutcome_ge_iff_MiserePlayerOutcome_ge.mp (h10 x hx) .left
      -- and hence o^R(H + X) = R.
      have h12 : MiserePlayerOutcome (hr + x) .left = .right := by
        have h13 : MiserePlayerOutcome (hr + x) .left ≤ .right := by
          simpa [h8] using h11
        exact Player.le_right_eq _ h13
      exact MiserePlayerOutcome_moves_right (add_right_mem_moves_add h9 x) h12
    · -- or else there exists some G^RL with G^RL ≥A H
      intro ⟨grl, h9, h10⟩
      -- In the latter, we observe that o^R(G^RL + X) = R (since o^L(G^R + X) = R),
      have h11 : MiserePlayerOutcome (grl + x) .right = .right := by
        simp [MiserePlayerOutcome] at h8
        rw [not_WinsGoingFirst] at h8
        have h8 := h8.right (grl + x) (add_right_mem_moves_add h9 x)
        rw [Player.neg_left, <-MiserePlayerOutcome_eq_iff_WinsGoingFirst] at h8
        exact h8
      -- and so o^R(H + X) ≤ o(G^RL + X) = R.
      have h12 := MisereOutcome_ge_iff_MiserePlayerOutcome_ge.mp (h10 x hx) .right
      rw [h11] at h12
      simp [h12]
  · -- 3. G + X is Right end-like.
    intro h7
    -- Since X ∈ A, it must follow that X is a Right end and G is Right end-like.
    have ⟨h8, h9⟩ := IsEnd.add_iff.mp h7
    -- By hypothesis, H is Right A-strong, and hence o^R(H + X) = R.
    have h11 := h4 h8 x hx h9
    rwa [MiserePlayerOutcome_eq_iff_WinsGoingFirst]
termination_by (x, (0 : Nat))
decreasing_by
  all_goals
    first
    | form_wf

private theorem auxL (A : GameForm → Prop) [Hereditary A]
    {g h x : GameForm}
    (hx : A x)
    (h2 : Maintenance A g h .right) (h3 : Maintenance A g h .left)
    (h4 : Proviso A g h .right) (h5 : Proviso A h g .left)
    (h6 : MiserePlayerOutcome (h + x) .left = .left)
    : MiserePlayerOutcome (g + x) .left = .left := by
  -- We must be in one of three cases:
  apply Or.elim3 (auxCases h6)
  · -- 1. o^R(H + X^L) = L for some X^L.
    intro ⟨xl, h7, h8⟩
    rw [Player.neg_left] at h8
    -- By induction on X^L, since A is hereditary, we have o^R(G + X^L) = L.
    have h9 : MiserePlayerOutcome (g + xl) .right ≥ MiserePlayerOutcome (h + xl) .right := by
      exact MisereOutcome_ge_iff_MiserePlayerOutcome_ge.mp
        (aux A h2 h3 h4 h5
          (Hereditary.has_option hx (IsOption.of_mem_moves h7))) .right
    have h10 : MiserePlayerOutcome (g + xl) .right = .left := by
      have h11 : .left ≤ MiserePlayerOutcome (g + xl) .right := by
        simpa [h8] using h9
      exact Player.le_left_eq _ h11
    -- and hence oL(G + X) = L.
    exact MiserePlayerOutcome_moves_left (add_left_mem_moves_add h7 g) h10
  · -- 2. o^R(H^L + X) = L for some H^L.
    intro ⟨hl, h7, h8⟩
    rw [Player.neg_left] at h8
    -- By hypothesis,
    apply Or.elim (h3 hl h7)
    · -- either there exists some G^L with G^L ≥A HL,
      intro ⟨gl, h9, h10⟩
      -- In the first case, we have immediately that o^R(G^L + X) ≥ o^R(H^L + X),
      have h11 : MiserePlayerOutcome (gl + x) .right ≥ MiserePlayerOutcome (hl + x) .right := by
        exact MisereOutcome_ge_iff_MiserePlayerOutcome_ge.mp (h10 x hx) .right
      -- and hence o^L(G + X) = L.
      refine MiserePlayerOutcome_moves_left (add_right_mem_moves_add h9 x) ?_
      simp [h8] at h11
      simp [h11]
    · -- or else there exists some H^LR with G ≥A H^LR
      intro ⟨hlr, h9, h10⟩
      -- In the latter, we observe that o^L(H^LR + X) = L (since o^R(H^L + X) = L ),
      have h11 : MiserePlayerOutcome (hlr + x) .left = .left := by
        simp [MiserePlayerOutcome] at h8
        rw [not_WinsGoingFirst] at h8
        have h8 := h8.right (hlr + x) (add_right_mem_moves_add h9 x)
        rw [Player.neg_right, <-MiserePlayerOutcome_eq_iff_WinsGoingFirst] at h8
        exact h8
      -- and so o^L(G + X) ≥ o(H^LR + X) = L.
      have h12 := MisereOutcome_ge_iff_MiserePlayerOutcome_ge.mp (h10 x hx) .left
      rw [h11] at h12
      simp [h12]
  · -- 3. H + X is Left end-like.
    intro h7
    -- Since X ∈ A, it must follow that X is a Left end and H is Left end-like.
    have ⟨h8, h9⟩ := IsEnd.add_iff.mp h7
    -- By hypothesis, G is Left A-strong, and hence o^L(G + X) = L.
    have h11 := h5 h8 x hx h9
    rwa [MiserePlayerOutcome_eq_iff_WinsGoingFirst]
termination_by (x, (0 : Nat))
decreasing_by
  all_goals
    first
    | form_wf

private theorem aux (A : GameForm → Prop) [Hereditary A]
    {g h x : GameForm}
    (h2 : Maintenance A g h .right) (h3 : Maintenance A g h .left)
    (h4 : Proviso A g h .right) (h5 : Proviso A h g .left)
    (hx : A x)
    : MisereOutcome (g + x) ≥ MisereOutcome (h + x) := by
  rw [MisereOutcome_ge_iff_MiserePlayerOutcome_ge]
  intro p; cases p
  · cases h6 : MiserePlayerOutcome (h + x) Player.left
    · simp [auxL A hx h2 h3 h4 h5 h6]
    · simp
  · cases h6 : MiserePlayerOutcome (g + x) Player.right
    · simp
    · simp [auxR A hx h2 h3 h4 h5 h6]
termination_by (x, (1 : Nat))
decreasing_by
  all_goals
    first
    | form_wf

end

theorem Hereditary.MisereGe (A : GameForm → Prop) [Hereditary A]
    {g h : GameForm}
    (h2 : Maintenance A g h .right) (h3 : Maintenance A g h .left)
    (h4 : Proviso A g h .right) (h5 : Proviso A h g .left)
    : g ≥m A h := by
  intro x hx
  exact aux A h2 h3 h4 h5 hx
