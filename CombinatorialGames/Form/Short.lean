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

namespace Form

open Form

variable {G : Type u} [g_form : Form G]

def ShortAux (x : G) : Prop :=
  ∀ p, (Form.moves p x).Finite ∧ ∀ y ∈ Form.moves p x, ShortAux y
termination_by x
decreasing_by form_wf

/-- A short game is one with finitely many subpositions. That is, the left and right sets are
finite, and all of the games in them are short as well. -/
@[mk_iff short_iff_aux]
class Short (x : G) : Prop where of_shortAux ::
  out : ShortAux x

theorem short_def {x : G} : Short x ↔ ∀ p, (Form.moves p x).Finite ∧ ∀ y ∈ Form.moves p x, Short y := by
  simp_rw [short_iff_aux]; rw [ShortAux]

alias ⟨_, Short.mk⟩ := short_def

namespace Short
variable {x y : G}

theorem finite_moves (p : Player) (x : G) [h : Short x] : (Form.moves p x).Finite :=
  (short_def.1 h p).1

theorem finite_setOf_isOption (x : G) [Short x] : {y | Form.IsOption y x}.Finite := by
  simp_rw [Form.isOption_iff_mem_union]
  exact (finite_moves _ x).union (finite_moves _ x)

instance (p : Player) (x : G) [Short x] : Finite (Form.moves p x) :=
  (Short.finite_moves _ x).to_subtype

instance (x : G) [Short x] : Finite {y // Form.IsOption y x} :=
  (Short.finite_setOf_isOption x).to_subtype

protected theorem of_mem_moves [h : Short x] {p} (hy : y ∈ Form.moves p x) : Short y :=
  (short_def.1 h p).2 y hy

protected theorem isOption [Short x] (h : Form.IsOption y x) : Short y := by
  simp_rw [Form.isOption_iff_mem_union] at h
  cases h with
  | inl h => exact .of_mem_moves h
  | inr h => exact .of_mem_moves h

alias _root_.Form.IsOption.short := Short.isOption

protected theorem subposition [Short x] (h : Subposition y x) : Short y := by
  sorry
--  cases h with
--  | single h => exact Short.isOption h
--  | tail IH h => have := Short.isOption h; exact Short.subposition IH
--termination_by x
--decreasing_by form_wf

alias _root_.Form.IsOption.subposition := Short.subposition

theorem finite_setOf_subposition (x : G) [Short x] : {y | Form.Subposition y x}.Finite := by
  have : {y | Form.Subposition y x} = {y | Form.IsOption y x} ∪
      ⋃ y ∈ {y | Form.IsOption y x}, {z | Form.Subposition z y} := by
    ext
    rw [Set.mem_setOf_eq, Form.Subposition, Relation.transGen_iff]
    simp [and_comm]
  rw [this]
  refine (finite_setOf_isOption x).union <| (finite_setOf_isOption x).biUnion fun y hy ↦ ?_
  have := Short.isOption hy
  exact finite_setOf_subposition y
termination_by x
decreasing_by form_wf

instance (x : G) [Short x] : Finite {y // Form.Subposition y x} :=
  (Short.finite_setOf_subposition x).to_subtype

theorem _root_.Form.short_iff_finite_setOf_subposition {x : G} :
    Short x ↔ {y | Form.Subposition y x}.Finite := by
  refine ⟨@finite_setOf_subposition _ _ x, fun h ↦ mk fun p ↦ ⟨?_, ?_⟩⟩
  on_goal 1 => refine h.subset fun y hy ↦ ?_
  on_goal 2 => refine fun y hy ↦ short_iff_finite_setOf_subposition.2 <| h.subset fun z hz ↦ ?_
  all_goals form_wf
termination_by x
decreasing_by form_wf

end Short
end Form

namespace GameForm
open Form (Short)
variable {x y : GameForm}

-- TODO: old proof was simply `rw [short_def]; simp`, but I didn't see how to
-- get it to recognise GameForm.moves as Form.moves and vice versa without
-- using change... Surely it is very simple?
@[simp]
protected instance Short.zero : Short (0 : GameForm) := by
  rw [Form.short_def]
  intro p
  constructor
  · change (GameForm.moves p 0).Finite; rw [moves_zero]; exact Set.finite_empty
  · intro y hy; change y ∈ GameForm.moves p 0 at hy; rw [moves_zero] at hy; exact False.elim hy

@[simp]
protected instance Short.one : Short (1 : GameForm) := by
  rw [Form.short_def]
  intro p
  change (GameForm.moves p 1).Finite ∧ ∀ y ∈ GameForm.moves p 1, Short y
  cases p with
  | left => simp [leftMoves_one, Set.finite_singleton, Short.zero]
  | right => simp [rightMoves_one, Set.finite_empty]

-- TODO: rewrite like old version (didn't seem to port trivially)
-- TODO: we are blocked for doing this for AugmentedForm until neg is
-- implemented. Should neg be added to Form?
protected instance Short.neg (x : GameForm) [Short x] : Short (-x) := by
  rw [Form.short_def]
  intro p
  constructor
  · change (GameForm.moves p (-x)).Finite; rw [GameForm.moves_neg]
    simpa [← Set.image_neg_eq_neg] using (Short.finite_moves _ x).image _
  · intro y hy
    change y ∈ GameForm.moves p (-x) at hy; rw [GameForm.moves_neg] at hy
    have h_neg_y : -y ∈ GameForm.moves (-p) x := by simp [Set.mem_neg] at hy; exact hy
    have : Short (-y) := Short.of_mem_moves h_neg_y
    simpa using Short.neg (-y)
termination_by x
decreasing_by form_wf

@[simp]
theorem Short.neg_iff {x : GameForm} : Short (-x) ↔ Short x :=
  ⟨fun _ ↦ by simpa using Short.neg (-x), fun _ ↦ Short.neg x⟩

-- TODO: rewrite like old version (didn't seem to port trivially)
-- TODO: should add be added to Form?
protected instance Short.add (x y : GameForm) [Short x] [Short y] : Short (x + y) := by
  rw [Form.short_def]
  intro p
  constructor
  · change (GameForm.moves p (x + y)).Finite; rw [GameForm.moves_add]
    exact ((Short.finite_moves p x).image _).union ((Short.finite_moves p y).image _)
  · intro z hz
    change z ∈ GameForm.moves p (x + y) at hz; rw [GameForm.moves_add] at hz
    cases hz with
    | inl h => 
      obtain ⟨a, ha, rfl⟩ := h
      have : Short a := Short.of_mem_moves ha
      exact Short.add a y
    | inr h => 
      obtain ⟨b, hb, rfl⟩ := h
      have : Short b := Short.of_mem_moves hb
      exact Short.add x b
termination_by (x, y)
decreasing_by form_wf

protected instance Short.sub (x y : GameForm) [Short x] [Short y] : Short (x - y) :=
  Short.add ..

protected instance Short.natCast : ∀ n : ℕ, Short (n : GameForm)
  | 0 => inferInstanceAs (Short (0 : GameForm))
  | n + 1 => have := Short.natCast n; inferInstanceAs (Short ((n + 1) : GameForm))

protected instance Short.ofNat (n : ℕ) [n.AtLeastTwo] : Short (ofNat(n) : GameForm) :=
  inferInstanceAs (Short (n : GameForm))

protected instance Short.intCast : ∀ n : ℤ, Short (n : GameForm)
  | .ofNat n => inferInstanceAs (Short (n : GameForm))
  | .negSucc n => inferInstanceAs (Short (-(n + 1 : GameForm)))

end GameForm
