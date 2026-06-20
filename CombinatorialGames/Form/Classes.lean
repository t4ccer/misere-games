/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Form

universe u

public section

namespace Form

variable {G : Type (u + 1)} [Form G]

/--
The ambient space of all games, imposing no restriction. This is the
counterpart of `IsShort`.
-/
@[expose] def IsLong (_ : G) : Prop := True

omit [Form G] in
@[simp] theorem isLong (g : G) : IsLong g := trivial

class HasZero (A : G → Prop) where
  has_zero : A (0 : G)

class HasNat (A : G → Prop) where
  has_nat (n : ℕ) : A (n : G)

class HasInt (A : G → Prop) where
  has_int (n : ℤ) : A (n : G)

instance {A : G → Prop} [HasNat A] : HasZero A where
  has_zero := by exact_mod_cast HasNat.has_nat (A := A) 0

instance {A : G → Prop} [HasInt A] : HasNat A where
  has_nat n := HasInt.has_int n

instance : HasInt (IsLong : G → Prop) where
  has_int _ := trivial

theorem HasInt.has_neg_int {A : G → Prop} [HasInt A] (n : ℕ) : A (-(n : G)) := by
  have hi := HasInt.has_int (A := A) (-(n : ℤ))
  rwa [Form.intCast_neg, Form.intCast_nat] at hi

theorem has_one {A : G → Prop} [HasNat A] : A 1 := by
  rw [<-Nat.cast_one]
  exact HasNat.has_nat 1

class ClosedUnderAddNat {G : Type (u + 1)} [Form G] (A : G → Prop) where
  has_add {g : G} (h1 : A g) (n : ℕ) : A (g + n)

instance : ClosedUnderAddNat (IsLong : G → Prop) where
  has_add _ _ := trivial

class ClosedUnderAdd (A : G → Prop) where
  has_add (g h : G) (h_g : A g) (h_h : A h) : A (g + h)

instance : ClosedUnderAdd (IsLong : G → Prop) where
  has_add _ _ _ _ := trivial

variable {A : G → Prop}

class Hereditary (A : G → Prop) where
  has_option {g g' : G} (h1 : A g) (h2 : Moves.IsOption g' g) : A g'

theorem Hereditary.of_mem_moves {A : G → Prop} [Hereditary A]
  {p : Player} {g g' : G} (hA : A g) (h_mem : g' ∈ moves p g) : A g' :=
  Hereditary.has_option hA (IsOption.of_mem_moves h_mem)

instance : Hereditary (IsLong : G → Prop) where
  has_option _ _ := trivial

private theorem exists_isZeroLike_of_mem [Hereditary A] {g : G} (hg : A g) :
    ∃ z, A z ∧ IsZeroLike z := by
  by_cases hz : IsZeroLike g
  · exact ⟨g, hg, hz⟩
  · simp only [IsZeroLike, not_forall] at hz
    obtain ⟨p, hp⟩ := hz
    obtain ⟨gp, hgp⟩ := not_isEnd_exists_move hp
    exact exists_isZeroLike_of_mem (Hereditary.of_mem_moves hg hgp)
termination_by g
decreasing_by form_wf

/--
A nonempty hereditary set of forms contains a zero-like form.
-/
theorem exists_isZeroLike [Hereditary A] (h : ∃ g, A g) : ∃ z, A z ∧ IsZeroLike z :=
  let ⟨_, hg⟩ := h
  exists_isZeroLike_of_mem hg

class ClosedUnderNeg (A : G → Prop) where
  neg_of {g : G} (h1 : A g) : A (-g)

instance : ClosedUnderNeg (IsLong : G → Prop) where
  neg_of _ := trivial

@[simp, nolint simpVarHead] -- It does fire, despite what linter comment says
theorem ClosedUnderNeg.neg_iff {A : G → Prop} [ClosedUnderNeg A] {g : G}
    : A (-g) ↔ A g := by
  constructor
  · intro h1
    have h2 := ClosedUnderNeg.neg_of h1
    rwa [neg_neg (G := G)] at h2
  · exact ClosedUnderNeg.neg_of

theorem HasInt.of_hasNat {A : G → Prop} [HasNat A] [ClosedUnderNeg A] : HasInt A where
  has_int n := by
    obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg <;>
      simpa using HasNat.has_nat (A := A) k

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
