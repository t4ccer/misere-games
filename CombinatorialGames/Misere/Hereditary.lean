/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import CombinatorialGames.Form.Short
public import CombinatorialGames.Form.Misere.Outcome

public section

universe u

open Form
open Form.Misere.Outcome

namespace Form

variable {G : Type (u + 1)} [Form G]

@[expose] def Maintenance (A : G → Prop) (g h : G) (p : Player) : Prop :=
  match p with
  | .right => ∀ gr ∈ moves .right g,
      (∃ hr ∈ moves .right h, gr ≥m A hr) ∨
      (∃ grl ∈ moves .left gr, grl ≥m A h)
  | .left => ∀ hl ∈ moves .left h,
      (∃ gl ∈ moves .left g, gl ≥m A hl) ∨
      (∃ hlr ∈ moves .right hl, g ≥m A hlr)

@[expose] def Strong (A : G → Prop) (g : G) (p : Player) : Prop :=
  ∀ x, A x → IsEndLike p x → WinsGoingFirst p (g + x)

@[expose] def Proviso (A : G → Prop) (g h : G) (p : Player) : Prop :=
  IsEndLike p g → Strong A h p

class Hereditary (A : G → Prop) where
  has_option {g g' : G} (h1 : A g) (h2 : Moves.IsOption g' g) : A g'

instance : Hereditary (fun _ => True) (G := G) where
  has_option _ _ := trivial

instance : Hereditary IsShort (G := G) where
  has_option := Moves.IsOption.short

private theorem auxCases {h x : G} {p : Player} (h1 : MiserePlayerOutcome (h + x) p = p)
    : (∃ xl ∈ moves p x, MiserePlayerOutcome (h + xl) (-p) = p)
    ∨ (∃ hl ∈ moves p h, MiserePlayerOutcome (hl + x) (-p) = p)
    ∨ (IsEndLike p (h + x)) := by
  apply Or.elim ((winsGoingFirst_iff _ _).mp (miserePlayerOutcome_eq_iff_winsGoingFirst.mp h1))
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

private theorem auxR (A : G → Prop) [Hereditary A]
    {g h x : G}
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
      exact misereOutcome_ge_iff_miserePlayerOutcome_ge.mp
        (aux A h2 h3 h4 h5
          (Hereditary.has_option hx (IsOption.of_mem_moves h7))) .left
    have h10 : MiserePlayerOutcome (h + xr) .left = .right := by
      have h11 : MiserePlayerOutcome (h + xr) .left ≤ .right := by
        simpa [h8] using h9
      exact Player.le_right_eq _ h11
    -- and hence oR(H + X) = R.
    exact miserePlayerOutcome_of_rightMoves (add_left_mem_moves_add h7 h) h10
  · -- 2. o^L(G^R + X) = R for some G^R.
    intro ⟨gr, h7, h8⟩
    rw [Player.neg_right] at h8
    -- By hypothesis,
    apply Or.elim (h2 gr h7)
    · -- either there exists some H^R with G^R ≥A H^R,
      intro ⟨hr, h9, h10⟩
      -- In the first case, we have immediately that o^L(G^R + X) ≥ o^L(H^R + X),
      have h11 : MiserePlayerOutcome (gr + x) .left ≥ MiserePlayerOutcome (hr + x) .left := by
        exact misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (h10 x hx) .left
      -- and hence o^R(H + X) = R.
      have h12 : MiserePlayerOutcome (hr + x) .left = .right := by
        have h13 : MiserePlayerOutcome (hr + x) .left ≤ .right := by
          simpa [h8] using h11
        exact Player.le_right_eq _ h13
      exact miserePlayerOutcome_of_rightMoves (add_right_mem_moves_add h9 x) h12
    · -- or else there exists some G^RL with G^RL ≥A H
      intro ⟨grl, h9, h10⟩
      -- In the latter, we observe that o^R(G^RL + X) = R (since o^L(G^R + X) = R),
      have h11 : MiserePlayerOutcome (grl + x) .right = .right := by
        simp [MiserePlayerOutcome] at h8
        rw [not_winsGoingFirst_iff] at h8
        have h8 := h8.right (grl + x) (add_right_mem_moves_add h9 x)
        rw [Player.neg_left, <-miserePlayerOutcome_eq_iff_winsGoingFirst] at h8
        exact h8
      -- and so o^R(H + X) ≤ o(G^RL + X) = R.
      have h12 := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (h10 x hx) .right
      rw [h11] at h12
      simp [h12]
  · -- 3. G + X is Right end-like.
    intro h7
    -- Since X ∈ A, it must follow that X is a Right end and G is Right end-like.
    rw [IsEndLike.add_iff] at h7
    have ⟨h8, h9⟩ := h7
    -- By hypothesis, H is Right A-strong, and hence o^R(H + X) = R.
    have h11 := h4 h8 x hx h9
    rwa [miserePlayerOutcome_eq_iff_winsGoingFirst]
termination_by (x, (0 : Nat))
decreasing_by
  all_goals
    first
    | form_wf

private theorem auxL (A : G → Prop) [Hereditary A]
    {g h x : G}
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
      exact misereOutcome_ge_iff_miserePlayerOutcome_ge.mp
        (aux A h2 h3 h4 h5
          (Hereditary.has_option hx (IsOption.of_mem_moves h7))) .right
    have h10 : MiserePlayerOutcome (g + xl) .right = .left := by
      have h11 : .left ≤ MiserePlayerOutcome (g + xl) .right := by
        simpa [h8] using h9
      exact Player.le_left_eq _ h11
    -- and hence oL(G + X) = L.
    exact miserePlayerOutcome_of_leftMoves (add_left_mem_moves_add h7 g) h10
  · -- 2. o^R(H^L + X) = L for some H^L.
    intro ⟨hl, h7, h8⟩
    rw [Player.neg_left] at h8
    -- By hypothesis,
    apply Or.elim (h3 hl h7)
    · -- either there exists some G^L with G^L ≥A HL,
      intro ⟨gl, h9, h10⟩
      -- In the first case, we have immediately that o^R(G^L + X) ≥ o^R(H^L + X),
      have h11 : MiserePlayerOutcome (gl + x) .right ≥ MiserePlayerOutcome (hl + x) .right := by
        exact misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (h10 x hx) .right
      -- and hence o^L(G + X) = L.
      refine miserePlayerOutcome_of_leftMoves (add_right_mem_moves_add h9 x) ?_
      simp [h8] at h11
      simp [h11]
    · -- or else there exists some H^LR with G ≥A H^LR
      intro ⟨hlr, h9, h10⟩
      -- In the latter, we observe that o^L(H^LR + X) = L (since o^R(H^L + X) = L ),
      have h11 : MiserePlayerOutcome (hlr + x) .left = .left := by
        simp [MiserePlayerOutcome] at h8
        rw [not_winsGoingFirst_iff] at h8
        have h8 := h8.right (hlr + x) (add_right_mem_moves_add h9 x)
        rw [Player.neg_right, <-miserePlayerOutcome_eq_iff_winsGoingFirst] at h8
        exact h8
      -- and so o^L(G + X) ≥ o(H^LR + X) = L.
      have h12 := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (h10 x hx) .left
      rw [h11] at h12
      simp [h12]
  · -- 3. H + X is Left end-like.
    intro h7
    -- Since X ∈ A, it must follow that X is a Left end and H is Left end-like.
    rw [IsEndLike.add_iff] at h7
    have ⟨h8, h9⟩ := h7
    -- By hypothesis, G is Left A-strong, and hence o^L(G + X) = L.
    have h11 := h5 h8 x hx h9
    rwa [miserePlayerOutcome_eq_iff_winsGoingFirst]
termination_by (x, (0 : Nat))
decreasing_by
  all_goals
    first
    | form_wf

private theorem aux (A : G → Prop) [Hereditary A]
    {g h x : G}
    (h2 : Maintenance A g h .right) (h3 : Maintenance A g h .left)
    (h4 : Proviso A g h .right) (h5 : Proviso A h g .left)
    (hx : A x)
    : MisereOutcome (g + x) ≥ MisereOutcome (h + x) := by
  rw [misereOutcome_ge_iff_miserePlayerOutcome_ge]
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

-- TODO: Move, this doesn't require the set to be hereditary

theorem proviso_right_of_misereGE {A : G → Prop}
    {g h : G} (hge : g ≥m A h) :
    Proviso A g h .right := by
  intro hg_end x hx hx_end
  have hgt : MiserePlayerOutcome (g + x) .right = .right :=
    miserePlayerOutcome_eq_iff_winsGoingFirst.mpr
      (winsGoingFirst_of_isEndLike (IsEndLike.add_iff.mpr ⟨hg_end, hx_end⟩))
  have h_cmp := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (hge x hx) .right
  rw [hgt] at h_cmp
  exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp (Player.le_right_eq _ h_cmp)

theorem proviso_left_of_misereGE {A : G → Prop}
    {g h : G} (hge : g ≥m A h) :
    Proviso A h g .left := by
  intro hh_end x hx hx_end
  have hht : MiserePlayerOutcome (h + x) .left = .left :=
    miserePlayerOutcome_eq_iff_winsGoingFirst.mpr
      (winsGoingFirst_of_isEndLike (IsEndLike.add_iff.mpr ⟨hh_end, hx_end⟩))
  have h_cmp := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (hge x hx) .left
  rw [hht] at h_cmp
  exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp (Player.le_left_eq _ h_cmp)

namespace Hereditary

theorem misereGE_of_maintenance_proviso (A : G → Prop) [Hereditary A]
    {g h : G}
    (h2 : Maintenance A g h .right) (h3 : Maintenance A g h .left)
    (h4 : Proviso A g h .right) (h5 : Proviso A h g .left)
    : g ≥m A h := by
  intro x hx
  exact aux A h2 h3 h4 h5 hx

theorem misereGE_of_moves {A : GameForm → Prop} [Hereditary A] {g h : GameForm}
    (hl1 : ∀ gl ∈ moves .left g, ∃ hl, hl ∈ moves .left h)
    (hl2 : ∀ hl ∈ moves .left h, ∃ gl ∈ moves .left g, gl ≥m A hl)
    (hr1 : ∀ gr ∈ moves .right g, ∃ hr ∈ moves .right h, gr ≥m A hr)
    (hr2 : ∀ hr ∈ moves .right h, ∃ gr, gr ∈ moves .right g)
    : g ≥m A h := by
  refine misereGE_of_maintenance_proviso A ?_ ?_ ?_ ?_
  · intro gr h1
    apply Or.inl
    have ⟨hr, h3, h4⟩ := hr1 gr h1
    use hr, h3
  · intro hl h1
    apply Or.inl
    have ⟨hr, h3, h4⟩ := hl2 hl h1
    use hr, h3
  · intro h2 y hy h1
    rw [GameForm.isEndLike_iff_isEnd] at h2 h1
    refine winsGoingFirst_add_of_isEnd (isEnd_of_not_mem ?_) h1
    simpa only [h2, not_mem_moves_of_isEnd, exists_const, imp_false] using hr2
  · intro h2 y hy h1
    rw [GameForm.isEndLike_iff_isEnd] at h2 h1
    refine winsGoingFirst_add_of_isEnd (isEnd_of_not_mem ?_) h1
    simpa only [h2, not_mem_moves_of_isEnd, exists_const, imp_false] using hl1

private theorem misereEQ_of_moves.aux {A : GameForm → Prop} [Hereditary A] {g h : GameForm}
    (hl1 : ∀ gl ∈ moves .left g, ∃ hl ∈ moves .left h, gl =m A hl)
    (hl2 : ∀ hl ∈ moves .left h, ∃ gl ∈ moves .left g, hl =m A gl)
    (hr1 : ∀ gr ∈ moves .right g, ∃ hr ∈ moves .right h, gr =m A hr)
    (hr2 : ∀ hr ∈ moves .right h, ∃ gr ∈ moves .right g, hr =m A gr)
    : g ≥m A h := by
  apply misereGE_of_moves
  · intro gl h_gl
    have ⟨hl, h1, _⟩ := hl1 gl h_gl
    use hl, h1
  · intro hl h_hl
    have ⟨gl, h1, h2⟩ := hl2 hl h_hl
    use gl, h1, misereGE_of_misereEQ (MisereEQ.symm h2)
  · intro gr h_gr
    have ⟨hr, h1, h2⟩ := hr1 gr h_gr
    use hr, h1, misereGE_of_misereEQ h2
  · intro hr h_hr
    have ⟨gr, h1, h2⟩ := hr2 hr h_hr
    use gr, h1

theorem misereEQ_of_moves {A : GameForm → Prop} [Hereditary A] {g h : GameForm}
    (hl1 : ∀ gl ∈ moves .left g, ∃ hl ∈ moves .left h, gl =m A hl)
    (hl2 : ∀ hl ∈ moves .left h, ∃ gl ∈ moves .left g, hl =m A gl)
    (hr1 : ∀ gr ∈ moves .right g, ∃ hr ∈ moves .right h, gr =m A hr)
    (hr2 : ∀ hr ∈ moves .right h, ∃ gr ∈ moves .right g, hr =m A gr)
    : g =m A h := by
  apply MisereEq.of_antisymm
  · exact misereEQ_of_moves.aux hl1 hl2 hr1 hr2
  · exact misereEQ_of_moves.aux hl2 hl1 hr2 hr1

end Hereditary
