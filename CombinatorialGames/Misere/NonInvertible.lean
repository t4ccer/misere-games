/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/

import CombinatorialGames.Misere.Adjoint
import CombinatorialGames.Form.Misere.Outcome
import CombinatorialGames.GameForm.Adjoint

open GameForm.Adjoint
open GameForm.Misere.Outcome
open Form
open Form.Misere.Outcome

def AnyGame (_ : GameForm) := True

instance : ClosedUnderNeg AnyGame where
  neg_of _ _ := trivial

noncomputable def leftEnd_not_leftEnd_not_ge.auxT (g h : GameForm) : GameForm :=
  !{ Set.range fun hr : h.moves .right => (hr : GameForm)°
   | { !{∅ | Set.range fun gl : g.moves .left => (gl : GameForm)°} } }

instance short_auxT {g h : GameForm} [h1 : Short g] [h2 : Short h]
    : Short (leftEnd_not_leftEnd_not_ge.auxT g h) := by
  unfold leftEnd_not_leftEnd_not_ge.auxT
  refine short_def.mpr ?_
  intro p
  change (GameForm.moves p _).Finite ∧ ∀ y ∈ GameForm.moves p _, Short y
  constructor
  · cases p
    · simp only [GameForm.moves_ofSets, Player.cases]
      have : Finite (h.moves .right) := Short.finite_moves .right h
      exact Set.finite_range (fun hr : h.moves .right => (hr : GameForm)°)
    · simp only [GameForm.moves_ofSets, Player.cases, Set.finite_singleton]
  · intro gp h3
    cases p <;> simp at h3
    · obtain ⟨gp', h3, h4⟩ := h3
      rw [<-h4]
      have _ : Short gp' := Short.of_mem_moves h3
      exact short_adjoint gp'
    · rw [h3]
      refine short_def.mpr ?_
      intro p
      change (GameForm.moves p _).Finite ∧ ∀ y ∈ GameForm.moves p _, Short y
      constructor <;> cases p
      · simp only [GameForm.moves_ofSets, Player.cases, Set.finite_empty]
      · simp only [GameForm.moves_ofSets, Player.cases]
        have : Finite (g.moves .left) := Short.finite_moves .left g
        exact Set.finite_range (fun gl : g.moves .left => (gl : GameForm)°)
      · simp only [GameForm.moves_ofSets, Player.cases, Set.mem_empty_iff_false,
                   IsEmpty.forall_iff, implies_true]
      · simp only [GameForm.moves_ofSets, Player.cases, Set.mem_range, Subtype.exists,
                   exists_prop, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        intro gl h4
        have _ : Short gl := Short.of_mem_moves h4
        exact short_adjoint gl

theorem leftEnd_not_leftEnd_not_ge {A : GameForm → Prop} {g h : GameForm}
    (h0 : A (leftEnd_not_leftEnd_not_ge.auxT g h)) (h1 : IsEnd .left h)
    (h2 : ¬(IsEnd .left g)) : ¬(g ≥m A h) := by
  let t := !{ Set.range fun hr : h.moves .right => (hr : GameForm)°
            | { !{∅ | Set.range fun gl : g.moves .left => (gl : GameForm)°} } }

  -- First consider H + T
  have h3 : MisereForm.MisereOutcome (h + t) ≥ Outcome.P := by
    apply not_rightWinsGoingFirst_ge_P
    rw [WinsGoingFirst_def]
    simp only [moves_add, Set.mem_union, Set.mem_image, not_or, not_and, IsEnd.add_iff]
    apply And.intro (fun h3 => by
      simp [t, Set.singleton_ne_empty, not_false_eq_true, moves, IsEnd])
    simp only [Player.neg_right, exists_prop, not_exists, not_and, not_not]
    intro x h3
    apply Or.elim h3 <;> clear h3 <;> intro ⟨hr, h3, h4⟩ <;> rw [<-h4]
    · -- If Right moves to H^R + T, then Left has a winning response to H^R + (H^R)°
      refine outcome_eq_P_leftWinsGoingFirst ?_ (outcome_add_adjoint_eq_P hr)
      refine GameForm.add_left_mem_moves_add ?_ hr
      simp only [t, GameForm.leftMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop]
      exists hr
    · -- If instead Right moves to H + { | (G^L)°}, then Left wins outright,
      -- since (by the assumption on H) both components are Left ends
      apply add_end_WinsGoingFirst h1
      simp only [t, GameForm.rightMoves_ofSets, Set.mem_singleton_iff, Form.moves] at h3
      simp only [h3, GameForm.leftMoves_ofSets, IsEnd, Form.moves]
  -- Next consider G + T
  have h4 : MisereForm.MisereOutcome (g + t) ≤ Outcome.N := by
    apply rightWinsGoingFirst_outcome_le_N
    rw [WinsGoingFirst_def]
    apply Or.inr
    -- Right has a move to G + { | (G^L)° }
    use (g + !{∅ | Set.range fun gl : g.moves .left => (gl : GameForm)°})
    constructor
    · rw [WinsGoingFirst']
      simp only [Player.neg_right, GameForm.moves_add, GameForm.moves_ofSets, Player.cases,
        Set.image_empty, Set.union_empty, Set.image_eq_empty, Player.neg_left, Set.mem_image,
        exists_prop, exists_exists_and_eq_and, not_or, not_exists, not_and, not_not, Form.moves, IsEnd]
      apply And.intro h2
      intro gl h4
      -- from which Left's only options have the form G^L + { | (G^L)° }
      rw [WinsGoingFirst']
      apply Or.inr
      -- There must be at least one such option, by the assumption on G;
      -- and each such option has a mirror-image response by Right, to G^L + (G^L)°
      use (gl + gl°)
      simp only [Player.neg_right, GameForm.moves_add, GameForm.moves_ofSets, Player.cases,
        Set.mem_union, Set.mem_image, Set.mem_range, Subtype.exists, exists_prop,
        exists_exists_and_eq_and, Form.moves]
      refine And.intro ?_ (outcome_eq_P_not_WinsGoingFirst (outcome_add_adjoint_eq_P gl))
      apply Or.inr
      use gl
    · refine GameForm.add_left_mem_moves_add ?_ g
      simp only [t, GameForm.rightMoves_ofSets, Set.mem_singleton_iff]
  unfold MisereGe
  intro h5
  have h6 : MisereForm.MisereOutcome (g + t) ≥ Outcome.P :=
    Preorder.le_trans
      Outcome.P
      (MisereForm.MisereOutcome (h + t))
      (MisereForm.MisereOutcome (g + t)) h3 (h5 t h0)
  cases h7 : MisereForm.MisereOutcome (g + t)
  all_goals simp only [t, h7, LE.le, LT.lt, and_false, and_self, and_true, ge_iff_le,
                       ne_eq, not_false_eq_true, not_true_eq_false, or_false, or_self, or_true,
                       reduceCtorEq] at h4 h6

alias theorem6_6 := leftEnd_not_leftEnd_not_ge

theorem ClosedUnderNeg.rightEnd_not_rightEnd_not_ge {A : GameForm → Prop} [ClosedUnderNeg A]
    {g h : GameForm} (h0 : A (leftEnd_not_leftEnd_not_ge.auxT (-g) (-h)))
    (h1 : IsEnd .right h) (h2 : ¬(IsEnd .right g)) : ¬(h ≥m A g) := by
  unfold IsEnd at h1 h2
  have h3 : IsEnd .left (-h) := IsEnd_neg_iff_neg.mpr h1
  have h4 : ¬(IsEnd .left (-g)) := IsEnd_neg_iff_neg.not.mpr h2
  have h5 : ¬((-g) ≥m A (-h)) := leftEnd_not_leftEnd_not_ge h0 h3 h4
  exact (ClosedUnderNeg.neg_ge_neg_iff h g).not.mp h5

class EqZeroIdentical (A : GameForm → Prop) extends (ClosedUnderNeg A) where
  has_T_g_zero {g : GameForm} (h1 : A g) : A (leftEnd_not_leftEnd_not_ge.auxT g 0)

instance : EqZeroIdentical AnyGame where
  has_T_g_zero _ := trivial

instance : EqZeroIdentical Short where
  has_T_g_zero _ := short_auxT

theorem EqZeroIdentical.ne_zero_not_eq_zero {A : GameForm → Prop} [EqZeroIdentical A]
    {g : GameForm} (h0 : A g) (h1 : g ≠ 0) : ¬(g =m A 0) := by
  obtain ⟨p, h2⟩ := GameForm.ne_zero_not_end h1
  cases p
  · have h3 := leftEnd_not_leftEnd_not_ge (has_T_g_zero h0) GameForm.zero_end h2
    exact not_MisereEq_of_not_MisereGe h3
  · intro h3
    have h4 : A (-g) := EqZeroIdentical.toClosedUnderNeg.neg_of g h0
    have h5 : A (leftEnd_not_leftEnd_not_ge.auxT (-g) (-0)) := by
      rw [neg_zero]
      exact has_T_g_zero h4
    exact not_MisereEq_of_not_MisereGe
            (ClosedUnderNeg.rightEnd_not_rightEnd_not_ge h5 GameForm.zero_end h2)
            (MisereEq_symm h3)

theorem EqZeroIdentical.eq_zero_iff_identical_zero {A : GameForm → Prop} [EqZeroIdentical A]
    {g : GameForm} (h0 : A g) : (g =m A 0 ↔ g = 0) := by
  constructor <;> intro h2
  · by_contra h3
    exact ne_zero_not_eq_zero h0 h3 h2
  · rw [h2]
    intro _
    exact congrFun rfl

theorem Transfinite.eq_zero_iff_identical_zero {g : GameForm} :
    (g =m AnyGame 0 ↔ g = 0) := EqZeroIdentical.eq_zero_iff_identical_zero trivial

theorem Short.eq_zero_iff_identical_zero {g : GameForm} [h1 : Short g] :
    (g =m Short 0 ↔ g = 0) := EqZeroIdentical.eq_zero_iff_identical_zero h1
