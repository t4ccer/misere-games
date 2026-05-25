/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.Hereditary
import CombinatorialGames.GameForm.Birthday

universe u

public section

class ClosedUnderAdd (A : GameForm → Prop) where
  has_add (g h : GameForm) (h_g : A g) (h_h : A h) : A (g + h)

open Form

macro "additiveClosure_birthday" : tactic =>
  `(tactic|
    all_goals
    · try casesm* _ ∧ _;
      subst_vars;
      simp only [Form.birthday_add, lt_add_iff_pos_left, lt_add_iff_pos_right];
      by_contra h_absurd;
      simp only [not_lt, NatOrdinal.le_zero, GameForm.birthday_eq_zero] at h_absurd;
      contradiction)

set_option linter.unusedVariables false in -- Used in the terminaton proof
def AdditiveClosure (A : GameForm → Prop) (g : GameForm) : Prop :=
  A g
  ∨ (∃ x y, ∃ (h : x ≠ 0 ∧ y ≠ 0 ∧ g = x + y), AdditiveClosure A x ∧ AdditiveClosure A y)
termination_by Form.birthday g
decreasing_by additiveClosure_birthday

variable {A : GameForm → Prop}

theorem additiveClosure_iff {g : GameForm} :
    AdditiveClosure A g ↔
    A g ∨ (∃ x y, x ≠ 0 ∧ y ≠ 0 ∧ g = x + y ∧ AdditiveClosure A x ∧ AdditiveClosure A y) := by
  constructor
  · intro h; unfold AdditiveClosure at h;
    obtain h1 | ⟨x, y, ⟨hx, hy, hxy⟩, hax, hay⟩ := h
    · exact Or.inl h1
    · apply Or.inr
      use x, y
  · intro h; unfold AdditiveClosure
    obtain h1 | ⟨x, y, hx, hy, hxy, hax, hay⟩ := h
    · exact Or.inl h1
    · apply Or.inr
      use x, y

instance : ClosedUnderAdd (AdditiveClosure A) where
  has_add g h h_g h_h := by
    by_cases h_g_zero : g = 0
    · subst h_g_zero; rw [zero_add]
      exact h_h
    · by_cases h_h_zero : h = 0
      · subst h_h_zero; rw [add_zero]
        exact h_g
      · rw [additiveClosure_iff]
        apply Or.inr
        use g, h

private theorem has_option' [Hereditary A] {g g' : GameForm} (h_g : AdditiveClosure A g) (h_g' : IsOption g' g) :
    AdditiveClosure A g' := by
  rw [additiveClosure_iff] at h_g
  obtain h_g | ⟨a, b, ha, hb, hab, ha_closure, hb_closure⟩ := h_g
  · rw [additiveClosure_iff]
    apply Or.inl
    exact Hereditary.has_option h_g h_g'
  · simp [isOption_iff_mem_union, hab] at h_g'
    obtain (⟨x, h_x_mem, h_xh⟩ | ⟨x, h_x_mem, h_gx⟩) | ⟨x, h_x_mem, h_xh⟩ | ⟨x, h_x_mem, h_gx⟩ := h_g'
    · subst h_xh
      refine ClosedUnderAdd.has_add x b ?_ hb_closure
      exact has_option' ha_closure (IsOption.of_mem_moves h_x_mem)
    · subst h_gx
      refine ClosedUnderAdd.has_add a x ha_closure ?_
      exact has_option' hb_closure (IsOption.of_mem_moves h_x_mem)
    · subst h_xh
      refine ClosedUnderAdd.has_add x b ?_ hb_closure
      exact has_option' ha_closure (IsOption.of_mem_moves h_x_mem)
    · subst h_gx
      refine ClosedUnderAdd.has_add a x ha_closure ?_
      exact has_option' hb_closure (IsOption.of_mem_moves h_x_mem)
termination_by birthday g
decreasing_by additiveClosure_birthday

instance [Hereditary A] : Hereditary (AdditiveClosure A) where
  has_option := has_option'
