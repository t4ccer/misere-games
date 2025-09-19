/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Kim Morrison
-/

import CombinatorialGames.GameForm
import CombinatorialGames.Form
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Lattice

/-!
# Short games

A combinatorial game is `Short` if it has only finitely many subpositions. In particular, this means
there is a finite set of moves at every point.

We historically defined `Short x` as data, which we then used to enable some degree of computation
on combinatorial games. This functionality is now implemented through the `game_cmp` tactic instead.
-/

universe u

namespace GameForm

open Form

def ShortAux (x : GameForm) : Prop :=
  ∀ p, (x.moves p).Finite ∧ ∀ y ∈ x.moves p, ShortAux y
termination_by x
decreasing_by form_wf

/-- A short game is one with finitely many subpositions. That is, the left and right sets are
finite, and all of the games in them are short as well. -/
@[mk_iff short_iff_aux]
class Short (x : GameForm) : Prop where of_shortAux ::
  out : ShortAux x

theorem short_def {x : GameForm} : Short x ↔ ∀ p, (x.moves p).Finite ∧ ∀ y ∈ x.moves p, Short y := by
  simp_rw [short_iff_aux]; rw [ShortAux]

alias ⟨_, Short.mk⟩ := short_def

namespace Short
variable {x y : GameForm}

theorem finite_moves (p : Player) (x : GameForm) [h : Short x] : (x.moves p).Finite :=
  (short_def.1 h p).1

theorem finite_setOf_isOption (x : GameForm) [Short x] : {y | IsOption y x}.Finite := by
  simp_rw [IsOption.iff_mem_union]
  exact (finite_moves _ x).union (finite_moves _ x)

instance (p : Player) (x : GameForm) [Short x] : Finite (x.moves p) :=
  (Short.finite_moves _ x).to_subtype

instance (x : GameForm) [Short x] : Finite {y // IsOption y x} :=
  (Short.finite_setOf_isOption x).to_subtype

protected theorem of_mem_moves [h : Short x] {p} (hy : y ∈ x.moves p) : Short y :=
  (short_def.1 h p).2 y hy

protected theorem isOption [Short x] (h : IsOption y x) : Short y := by
  simp_rw [IsOption.iff_mem_union] at h
  cases h with
  | inl h => exact .of_mem_moves h
  | inr h => exact .of_mem_moves h

alias _root_.GameForm.IsOption.short := Short.isOption

protected theorem subposition {x : GameForm} [Short x] (h : Subposition y x) : Short y := by
  cases h with
  | single h => exact Short.isOption h
  | tail IH h => have := Short.isOption h; exact Short.subposition IH
termination_by x
decreasing_by form_wf

alias _root_.GameForm.IsOption.subposition := Short.subposition

theorem finite_setOf_subposition (x : GameForm) [Short x] : {y | Subposition y x}.Finite := by
  have : {y | Subposition y x} = {y | IsOption y x} ∪
      ⋃ y ∈ {y | IsOption y x}, {z | Subposition z y} := by
    ext
    rw [Set.mem_setOf_eq, Subposition, Relation.transGen_iff]
    simp [and_comm]
  rw [this]
  refine (finite_setOf_isOption x).union <| (finite_setOf_isOption x).biUnion fun y hy ↦ ?_
  have := Short.isOption hy
  exact finite_setOf_subposition y
termination_by x
decreasing_by form_wf

instance (x : GameForm) [Short x] : Finite {y // Subposition y x} :=
  (Short.finite_setOf_subposition x).to_subtype

theorem _root_.GameForm.short_iff_finite_setOf_subposition {x : GameForm} :
    Short x ↔ {y | Subposition y x}.Finite := by
  refine ⟨@finite_setOf_subposition x, fun h ↦ mk fun p ↦ ⟨?_, ?_⟩⟩
  on_goal 1 => refine h.subset fun y hy ↦ ?_
  on_goal 2 => refine fun y hy ↦ short_iff_finite_setOf_subposition.2 <| h.subset fun z hz ↦ ?_
  all_goals form_wf
termination_by x
decreasing_by form_wf

@[simp]
protected instance zero : Short 0 := by
  rw [short_def]; simp

@[simp]
protected instance one : Short 1 := by
  rw [short_def]; simp

protected instance neg (x : GameForm) [Short x] : Short (-x) := by
  refine mk fun p ↦ ⟨?_, ?_⟩
  · simpa [← Set.image_neg_eq_neg] using (finite_moves _ x).image _
  · rw [forall_moves_neg]
    intro y hy
    simpa using (Short.of_mem_moves hy).neg
termination_by x
decreasing_by form_wf

@[simp]
theorem neg_iff {x : GameForm} : Short (-x) ↔ Short x :=
  ⟨fun _ ↦ by simpa using Short.neg (-x), fun _ ↦ Short.neg x⟩

protected instance add (x y : GameForm) [Short x] [Short y] : Short (x + y) := by
  refine mk fun p ↦ ⟨?_, ?_⟩
  · simpa using ⟨(finite_moves _ x).image _, (finite_moves _ y).image _⟩
  · rw [forall_moves_add]
    constructor
    all_goals
      intro z hz
      have := Short.of_mem_moves hz
      exact Short.add ..
termination_by (x, y)
decreasing_by form_wf

protected instance sub (x y : GameForm) [Short x] [Short y] : Short (x - y) :=
  .add ..

protected instance natCast : ∀ n : ℕ, Short n
  | 0 => inferInstanceAs (Short 0)
  | n + 1 => have := Short.natCast n; inferInstanceAs (Short (n + 1))

protected instance ofNat (n : ℕ) [n.AtLeastTwo] : Short ofNat(n) :=
  inferInstanceAs (Short n)

protected instance intCast : ∀ n : ℤ, Short n
  | .ofNat n => inferInstanceAs (Short n)
  | .negSucc n => inferInstanceAs (Short (-(n + 1)))

end Short
end GameForm
