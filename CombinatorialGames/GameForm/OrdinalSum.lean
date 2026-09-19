/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.GameForm

/-!
# Ordinal sums

$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
The *ordinal sum* `G : H` of two game forms is played on `G` (the *base*) and
`H` (the *branch*) at once, but a move in the base destroys the branch:
$$
  G : H = \form<G^\mathcal{L}, G : H^\mathcal{L}>[G^\mathcal{R}, G : H^\mathcal{R}].
$$
Blue-Red Hackenbush stalks and forests are built from ordinal sums.
-/

universe u

public noncomputable section

namespace GameForm

open Form

/--
The ordinal sum `ordinalSum x y = x : y`, see the module docstring.
-/
def ordinalSum (x y : GameForm.{u}) : GameForm.{u} :=
  !{fun p ↦ moves p x ∪ Set.range fun z : moves p y ↦ ordinalSum x z.1}
termination_by y
decreasing_by form_wf

theorem moves_ordinalSum (p : Player) (x y : GameForm) :
    moves p (ordinalSum x y) = moves p x ∪ ordinalSum x '' moves p y := by
  rw [ordinalSum, moves_ofSets, Set.image_eq_range]

theorem mem_moves_ordinalSum_iff {p : Player} {x y z : GameForm} :
    z ∈ moves p (ordinalSum x y) ↔ z ∈ moves p x ∨ ∃ y' ∈ moves p y, z = ordinalSum x y' := by
  simp only [moves_ordinalSum, Set.mem_union, Set.mem_image, eq_comm]

theorem mem_moves_ordinalSum_base {p : Player} {x x' : GameForm} (y : GameForm)
    (h : x' ∈ moves p x) : x' ∈ moves p (ordinalSum x y) :=
  mem_moves_ordinalSum_iff.mpr (Or.inl h)

theorem mem_moves_ordinalSum_branch {p : Player} {y y' : GameForm} (x : GameForm)
    (h : y' ∈ moves p y) : ordinalSum x y' ∈ moves p (ordinalSum x y) :=
  mem_moves_ordinalSum_iff.mpr (Or.inr ⟨y', h, rfl⟩)

theorem isOption_ordinalSum_iff {x y z : GameForm} :
    IsOption z (ordinalSum x y) ↔ IsOption z x ∨ ∃ y', IsOption y' y ∧ z = ordinalSum x y' := by
  simp only [isOption_iff_mem_moves, mem_moves_ordinalSum_iff]
  constructor
  · rintro ⟨p, h | ⟨y', hy', rfl⟩⟩
    · exact Or.inl ⟨p, h⟩
    · exact Or.inr ⟨y', ⟨p, hy'⟩, rfl⟩
  · rintro (⟨p, h⟩ | ⟨y', ⟨p, hy'⟩, rfl⟩)
    · exact ⟨p, Or.inl h⟩
    · exact ⟨p, Or.inr ⟨y', hy', rfl⟩⟩

theorem IsOption.ordinalSum_base {x x' : GameForm} (y : GameForm) (h : IsOption x' x) :
    IsOption x' (ordinalSum x y) :=
  isOption_ordinalSum_iff.mpr (Or.inl h)

theorem IsOption.ordinalSum_branch {y y' : GameForm} (x : GameForm) (h : IsOption y' y) :
    IsOption (ordinalSum x y') (ordinalSum x y) :=
  isOption_ordinalSum_iff.mpr (Or.inr ⟨y', h, rfl⟩)

@[simp]
theorem isEnd_ordinalSum_iff {p : Player} {x y : GameForm} :
    IsEnd p (ordinalSum x y) ↔ IsEnd p x ∧ IsEnd p y := by
  simp only [isEnd_def, moves_ordinalSum, Set.union_empty_iff, Set.image_eq_empty]

@[simp]
theorem ordinalSum_zero (x : GameForm) : ordinalSum x 0 = x := by
  ext p
  simp only [moves_ordinalSum, moves_zero, Set.image_empty, Set.union_empty]

@[simp]
theorem zero_ordinalSum (y : GameForm) : ordinalSum 0 y = y := by
  ext p z
  simp only [mem_moves_ordinalSum_iff, moves_zero, Set.mem_empty_iff_false, false_or]
  constructor
  · rintro ⟨y', hy', rfl⟩
    rwa [zero_ordinalSum]
  · intro hz
    exact ⟨z, hz, (zero_ordinalSum z).symm⟩
termination_by y
decreasing_by form_wf

@[simp]
theorem ordinalSum_eq_zero_iff {x y : GameForm} : ordinalSum x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h_end : ∀ p, IsEnd p (ordinalSum x y) := fun p => h ▸ isEnd_zero
    simp only [isEnd_ordinalSum_iff] at h_end
    exact ⟨leftEnd_rightEnd_eq_zero (h_end .left).1 (h_end .right).1,
      leftEnd_rightEnd_eq_zero (h_end .left).2 (h_end .right).2⟩
  · rintro ⟨rfl, rfl⟩
    exact ordinalSum_zero 0

theorem ordinalSum_ne_zero {x : GameForm} (y : GameForm) (h : x ≠ 0) : ordinalSum x y ≠ 0 :=
  fun h' => h (ordinalSum_eq_zero_iff.mp h').1

theorem neg_ordinalSum (x y : GameForm) : -ordinalSum x y = ordinalSum (-x) (-y) := by
  ext p z
  simp only [moves_neg, Set.mem_neg, mem_moves_ordinalSum_iff]
  rw [Set.exists_neg_mem]
  refine or_congr Iff.rfl (exists_congr fun y' => and_congr_right fun hy' => ?_)
  rw [← neg_ordinalSum x y', neg_eq_iff_eq_neg]
termination_by y
decreasing_by form_wf

theorem ordinalSum_assoc (x y z : GameForm) :
    ordinalSum (ordinalSum x y) z = ordinalSum x (ordinalSum y z) := by
  ext p w
  simp only [mem_moves_ordinalSum_iff, or_assoc]
  constructor
  · rintro (h | ⟨y', hy', rfl⟩ | ⟨z', hz', rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y', Or.inl hy', rfl⟩
    · exact Or.inr ⟨ordinalSum y z', Or.inr ⟨z', hz', rfl⟩, ordinalSum_assoc x y z'⟩
  · rintro (h | ⟨w', hw' | ⟨z', hz', rfl⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨w', hw', rfl⟩)
    · exact Or.inr (Or.inr ⟨z', hz', (ordinalSum_assoc x y z').symm⟩)
termination_by z
decreasing_by form_wf

end GameForm
