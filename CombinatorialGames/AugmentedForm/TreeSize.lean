/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.AugmentedForm
public import CombinatorialGames.Form.Short

import Mathlib.Algebra.Order.BigOperators.Group.Finset

universe u

open Form
open Form.Misere.Outcome
open Classical

namespace AugmentedForm

public section

instance smallFinset {α : Type*} [Small.{u} α] : Small.{u} (Finset α) := by
  have hinj : Function.Injective (fun s : Finset α => s.image (equivShrink α)) := by
    intro a b h
    have := congrArg (fun t : Finset (Shrink α) => t.image (equivShrink α).symm) h
    simpa [Finset.image_image] using this
  exact small_of_injective hinj

noncomputable def treeSize (g : AugmentedForm.{u}) : NatOrdinal.{u+1} :=
  (if g.hasTombstone .left then 1 else 0) + (if g.hasTombstone .right then 1 else 0) + 1
    + (⨆ t : Finset (moves .left g), ∑ i ∈ t, treeSize i.1)
    + (⨆ t : Finset (moves .right g), ∑ i ∈ t, treeSize i.1)
termination_by g
decreasing_by form_wf

/--
For a finite small set, the supremum over finite subsets of the natural sum
equals the finite sum over the whole set.
-/
theorem iSup_finset_sum_eq {α : Type (u+1)} (s : Set α) [Small.{u} s] (hs : s.Finite)
    (f : α → NatOrdinal.{u+1}) :
    (⨆ t : Finset s, ∑ i ∈ t, f i.1) = ∑ x ∈ hs.toFinset, f x := by
  refine' le_antisymm _ _
  · refine' NatOrdinal.iSup_le_iff.2 fun t => _
    convert Finset.sum_le_sum_of_subset_of_nonneg _ _
    rotate_left
    exact hs.toFinset.preimage Subtype.val Subtype.val_injective.injOn
    · infer_instance
    · exact fun x hx => Finset.mem_preimage.mpr ( hs.mem_toFinset.mpr x.2 )
    · exact fun _ _ _ => NatOrdinal.zero_le _
    · refine Finset.sum_bij (fun x hx => ⟨x, hs.mem_toFinset.mp hx⟩) ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_preimage]; exact ha
      · intro a₁ ha₁ a₂ ha₂ hh
        exact congrArg Subtype.val hh
      · intro b hb
        rw [Finset.mem_preimage] at hb
        exact ⟨b.1, hb, Subtype.ext rfl⟩
      · intro a ha
        rfl
  · convert NatOrdinal.le_iSup _ ( hs.toFinset.subtype _ ) using 1
    · refine Finset.sum_bij (fun x hx => ⟨x, hs.mem_toFinset.mp hx⟩) ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_subtype]; exact ha
      · intro a₁ ha₁ a₂ ha₂ hh
        exact congrArg Subtype.val hh
      · intro b hb
        rw [Finset.mem_subtype] at hb
        exact ⟨b.1, hb, Subtype.ext rfl⟩
      · intro a ha
        rfl
    · exact smallFinset

/--
The supremum-over-finite-subsets natural sum is invariant under a bijection of
the underlying small sets that matches up the summed values.
-/
theorem iSup_finset_sum_congr {α β : Type (u+1)} (s : Set α) (t : Set β)
    [Small.{u} s] [Small.{u} t] (e : ↥t ≃ ↥s)
    (f : α → NatOrdinal.{u+1}) (g : β → NatOrdinal.{u+1})
    (he : ∀ x : t, f (e x).1 = g x.1) :
    (⨆ T : Finset s, ∑ i ∈ T, f i.1) = (⨆ T : Finset t, ∑ i ∈ T, g i.1) := by
  rw [← Equiv.iSup_comp (g := fun T : Finset s => ∑ i ∈ T, f i.1) (Equiv.finsetCongr e)]
  refine iSup_congr (fun T => ?_)
  rw [Equiv.finsetCongr_apply, Finset.sum_map]
  exact Finset.sum_congr rfl (fun x _ => he x)

theorem treeSize_eq {g : AugmentedForm.{u}} (h : IsShort g) :
    treeSize g =
      (if g.hasTombstone .left then 1 else 0) + (if g.hasTombstone .right then 1 else 0) + 1
      + (∑ x ∈ (Short.finite_moves .left h).toFinset, treeSize x)
      + (∑ x ∈ (Short.finite_moves .right h).toFinset, treeSize x) := by
  conv_lhs => rw [treeSize]
  rw [iSup_finset_sum_eq (moves .left g) (Short.finite_moves .left h),
      iSup_finset_sum_eq (moves .right g) (Short.finite_moves .right h)]

theorem one_le_treeSize {g : AugmentedForm.{u}} (h : IsShort g) : 1 ≤ treeSize g := by
  rw [treeSize_eq h]
  refine le_add_of_le_of_nonneg (le_add_of_le_of_nonneg ?_ ?_) ?_
  · exact NatOrdinal.le_add_left
  · exact NatOrdinal.zero_le _
  · exact NatOrdinal.zero_le _

theorem treeSize_neg {g : AugmentedForm.{u}} : treeSize (-g) = treeSize g := by
  conv_lhs => rw [treeSize]
  conv_rhs => rw [treeSize]
  rw [hasTombstone_neg_iff, hasTombstone_neg_iff]
  have hL : (⨆ T : Finset (moves .left (-g)), ∑ i ∈ T, treeSize i.1)
      = (⨆ T : Finset (moves .right g), ∑ i ∈ T, treeSize i.1) := by
    refine iSup_finset_sum_congr (moves .left (-g)) (moves .right g)
      ((Equiv.neg AugmentedForm).subtypeEquiv (fun a => by
        rw [moves_neg]; simp [Set.mem_neg, Player.neg_left])) treeSize treeSize ?_
    intro x
    rw [Equiv.subtypeEquiv_apply]
    exact treeSize_neg
  have hR : (⨆ T : Finset (moves .right (-g)), ∑ i ∈ T, treeSize i.1)
      = (⨆ T : Finset (moves .left g), ∑ i ∈ T, treeSize i.1) := by
    refine iSup_finset_sum_congr (moves .right (-g)) (moves .left g)
      ((Equiv.neg AugmentedForm).subtypeEquiv (fun a => by
        rw [moves_neg]; simp [Set.mem_neg, Player.neg_right])) treeSize treeSize ?_
    intro x
    rw [Equiv.subtypeEquiv_apply]
    exact treeSize_neg
  rw [hL, hR]
  simp only [Player.neg_left, Player.neg_right]
  ac_rfl
termination_by g
decreasing_by form_wf

theorem sum_leftMoves_add_one_le {g : AugmentedForm.{u}} (hg : IsShort g) :
    (∑ x ∈ (Short.finite_moves .left hg).toFinset, treeSize x) + 1 ≤ treeSize g := by
  classical
  rw [treeSize_eq hg]
  have e : (if g.hasTombstone .left then (1:NatOrdinal) else 0)
        + (if g.hasTombstone .right then 1 else 0) + 1
        + (∑ x ∈ (Short.finite_moves .left hg).toFinset, treeSize x)
        + (∑ x ∈ (Short.finite_moves .right hg).toFinset, treeSize x)
      = ((∑ x ∈ (Short.finite_moves .left hg).toFinset, treeSize x) + 1)
        + ((if g.hasTombstone .left then 1 else 0) + (if g.hasTombstone .right then 1 else 0)
          + (∑ x ∈ (Short.finite_moves .right hg).toFinset, treeSize x)) := by ac_rfl
  rw [e]
  exact NatOrdinal.le_add_right

end

end AugmentedForm
