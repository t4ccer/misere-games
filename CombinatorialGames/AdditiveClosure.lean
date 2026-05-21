/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Ruleset
public import CombinatorialGames.Misere.Hereditary
import CombinatorialGames.GameForm.Birthday

universe u

public section

class ClosedUnderAdd (A : GameForm → Prop) where
  has_add (g h : GameForm) (h_g : A g) (h_h : A h) : A (g + h)

namespace Ruleset

open Form

set_option linter.unusedVariables false in -- Used in the terminaton proof
def AdditiveClosure (R : Type u) [Ruleset R] (g : GameForm) : Prop :=
  (∃ (b : R), g = Ruleset.toGameForm b)
  ∨ (∃ x y, ∃ (h : x ≠ 0 ∧ y ≠ 0 ∧ g = x + y), AdditiveClosure R x ∧ AdditiveClosure R y)
termination_by Form.birthday g
decreasing_by
  · obtain ⟨_, h2, h3⟩ := h
    subst h3
    simp only [Form.birthday_add, lt_add_iff_pos_right]
    by_contra h4; simp only [not_lt, NatOrdinal.le_zero, GameForm.birthday_eq_zero] at h4
    exact h2 h4
  · obtain ⟨h1, _, h3⟩ := h
    subst h3
    simp only [Form.birthday_add, lt_add_iff_pos_left]
    by_contra h4; simp only [not_lt, NatOrdinal.le_zero, GameForm.birthday_eq_zero] at h4
    exact h1 h4

variable {R : Type u} [Ruleset R]

theorem additiveClosure_iff {g : GameForm} :
    AdditiveClosure R g ↔
    (∃ (b : R), g = Ruleset.toGameForm b)
    ∨ (∃ x y, x ≠ 0 ∧ y ≠ 0 ∧ g = x + y ∧ AdditiveClosure R x ∧ AdditiveClosure R y)
  := by
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

instance : ClosedUnderAdd (AdditiveClosure R) where
  has_add g h h_g h_h := by
    rw [additiveClosure_iff] at h_g h_h ⊢
    by_cases h_g_zero : g = 0
    · subst h_g_zero; rw [zero_add]
      by_cases h_h_zero : h = 0
      · subst h_h_zero
        apply Or.inl
        have ⟨r, hr⟩ := Ruleset.has_zero (R := R)
        use r
        exact hr.symm
      · obtain ⟨rh, h_h⟩ | ⟨x', y', hx', hy', hxy', hax', hay'⟩ := h_h
        · apply Or.inl; use rh
        · apply Or.inr; use x', y'
    · by_cases h_h_zero : h = 0
      · subst h_h_zero; rw [add_zero]
        obtain ⟨rg, h_g⟩ | ⟨x, y, hx, hy, hxy, hax, hay⟩ := h_g
        · apply Or.inl; use rg
        · apply Or.inr; use x, y
      · apply Or.inr
        rw [<-additiveClosure_iff] at h_g h_h
        use g, h

private theorem has_option' {g g' : GameForm} (h_g : AdditiveClosure R g) (h_g' : IsOption g' g) :
    AdditiveClosure R g' := by
  rw [additiveClosure_iff] at h_g
  obtain ⟨b, h_b⟩ | ⟨a, b, ha, hb, hab, ha_closure, hb_closure⟩ := h_g
  · rw [additiveClosure_iff]
    apply Or.inl
    simp only [isOption_iff_mem_union, Set.mem_union] at h_g'
    subst h_b
    obtain h_l | h_r := h_g'
    · have ⟨r', h_r'⟩ := Ruleset.moves_toGameForm .left b _ h_l
      use r', h_r'.symm
    · have ⟨r', h_r'⟩ := Ruleset.moves_toGameForm .right b _ h_r
      use r', h_r'.symm
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
decreasing_by
  all_goals
  · subst hab
    simp only [Form.birthday_add, lt_add_iff_pos_left, lt_add_iff_pos_right]
    by_contra h_absurd
    simp only [not_lt, NatOrdinal.le_zero, GameForm.birthday_eq_zero] at h_absurd
    absurd h_absurd
    assumption

instance : Hereditary (AdditiveClosure R) where
  has_option := has_option'

end Ruleset

