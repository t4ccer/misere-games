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

instance : Hereditary (fun _ => True) (G := G) where
  has_option _ _ := trivial
