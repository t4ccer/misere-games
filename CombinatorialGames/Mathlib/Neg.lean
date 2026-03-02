import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Logic.Small.Set

universe u

namespace Set

instance {α : Type*} [InvolutiveNeg α] (s : Set α) [Small.{u} s] : Small.{u} (-s :) := by
  rw [← Set.image_neg_eq_neg]
  infer_instance

@[simp]
theorem forall_mem_neg {α : Type*} [InvolutiveNeg α] {p : α → Prop} {s : Set α} :
    (∀ x, -x ∈ s → p x) ↔ ∀ x ∈ s, p (-x) := by
  rw [← (Equiv.neg _).forall_congr_right]
  simp

@[simp]
theorem exists_mem_neg {α : Type*} [InvolutiveNeg α] {p : α → Prop} {s : Set α} :
    (∃ x, -x ∈ s ∧ p x) ↔ ∃ x ∈ s, p (-x) := by
  rw [← (Equiv.neg _).exists_congr_right]
  simp

end Set
