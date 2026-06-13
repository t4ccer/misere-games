/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Form.Misere.Outcome

universe u

public section

namespace Form

variable {G : Type (u + 1)} [Form G]

class HasNat (A : G → Prop) where
  has_nat (n : ℕ) : A (n : G)

class HasInt (A : G → Prop) extends HasNat A where
  has_int (n : ℤ) : A (n : G)

theorem HasInt.has_neg_int {A : G → Prop} [HasInt A] (n : ℕ) : A (-(n : G)) := by
  have hi := HasInt.has_int (A := A) (-(n : ℤ))
  rwa [Form.intCast_neg, Form.intCast_nat] at hi

theorem has_one {A : G → Prop} [HasNat A] : A 1 := by
  rw [<-Nat.cast_one]
  exact HasNat.has_nat 1

class ClosedUnderAddNat {G : Type (u + 1)} [Form G] (A : G → Prop) where
  has_add {g : G} (h1 : A g) (n : ℕ) : A (g + n)

class ClosedUnderAdd (A : G → Prop) where
  has_add (g h : G) (h_g : A g) (h_h : A h) : A (g + h)

variable {A : G → Prop}

/-- Adding a fixed element `c ∈ A` on the right preserves the restricted misère inequality. -/
theorem misereGE_add_right [ClosedUnderAdd A] {g h c : G}
    (hc : A c) (h1 : g ≥m A h) : (g + c) ≥m A (h + c) := by
  intro x hx
  have hcx : A (c + x) := ClosedUnderAdd.has_add c x hc hx
  have := h1 (c + x) hcx
  rwa [← add_assoc, ← add_assoc] at this

/-- Adding a fixed element `c ∈ A` on the right preserves the restricted misère equivalence. -/
theorem misereEQ_add_right [ClosedUnderAdd A] {g h c : G}
    (hc : A c) (h1 : g =m A h) : (g + c) =m A (h + c) := by
  intro x hx
  have hcx : A (c + x) := ClosedUnderAdd.has_add c x hc hx
  have := h1 (c + x) hcx
  rwa [← add_assoc, ← add_assoc] at this

/-- Adding a fixed element `c ∈ A` on the left preserves the restricted misère equivalence. -/
theorem misereEQ_add_left [ClosedUnderAdd A] {g h c : G}
    (hc : A c) (h1 : g =m A h) : (c + g) =m A (c + h) := by
  have := misereEQ_add_right hc h1
  intro x hx
  have h2 := this x hx
  rwa [add_comm c g, add_comm c h]

class Hereditary (A : G → Prop) where
  has_option {g g' : G} (h1 : A g) (h2 : Moves.IsOption g' g) : A g'

theorem Hereditary.of_mem_moves {A : G → Prop} [Hereditary A]
  {p : Player} {g g' : G} (hA : A g) (h_mem : g' ∈ moves p g) : A g' :=
  Hereditary.has_option hA (IsOption.of_mem_moves h_mem)

instance : Hereditary (fun _ => True) (G := G) where
  has_option _ _ := trivial

theorem ClosedUnderAddNat.has_add_neg {A : G → Prop} [ClosedUnderAddNat A] [ClosedUnderNeg A]
    {g : G} (hAg : A g) (n : ℕ) :
    A (g + (-n)) := by
  have := ClosedUnderNeg.neg_of (ClosedUnderAddNat.has_add (ClosedUnderNeg.neg_of hAg) n)
  simp at this
  rwa [add_comm] at this

theorem ClosedUnderAddNat.has_add_int {A : G → Prop} [ClosedUnderAddNat A] [ClosedUnderNeg A] [HasInt A]
    {g : G} (hAg : A g) (n : ℤ) :
    A (g + n) := by
  match n with
  | .ofNat k =>
    simp only [Int.ofNat_eq_natCast, Form.intCast_nat]
    exact ClosedUnderAddNat.has_add hAg k
  | .negSucc k =>
    simp only [Form.intCast_negSucc, neg_add_rev]
    rw [<-Form.intCast_one, <-add_assoc, <-sub_eq_add_neg g, Form.intCast_ofNat, sub_eq_add_neg]
    have := ClosedUnderNeg.neg_of (ClosedUnderAddNat.has_add (ClosedUnderNeg.neg_of hAg) 1)
    simp only [neg_add_rev, neg_neg] at this
    rw [add_comm] at this
    exact ClosedUnderAddNat.has_add_neg this k

theorem ClosedUnderAddNat.has_add_int_neg {A : G → Prop} [ClosedUnderAddNat A] [ClosedUnderNeg A] [HasInt A]
    {g : G} (hAg : A g) (n : ℤ) :
    A (g + (-n)) := by
  have := ClosedUnderNeg.neg_of (ClosedUnderAddNat.has_add_int (ClosedUnderNeg.neg_of hAg) n)
  simp only [neg_add_rev, neg_neg] at this
  rwa [add_comm] at this
