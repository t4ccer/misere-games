/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.Closures
public import CombinatorialGames.Misere.Hereditary.MaintenanceProviso
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Directed

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Form.Misere.Outcome

public section

class Universe (IsAmbient : G → Prop) (A : G → Prop) extends
    ClosedUnderSum A, Hereditary A, ClosedUnderNeg A, ClosedUnderDicotic IsAmbient A where
  zero_mem : A 0
  isAmbient_of_mem {g : G} : A g → IsAmbient g

class LongUniverse (A : G → Prop) extends Universe (fun _ => True) A

class ShortUniverse (A : G → Prop) extends Universe IsShort A

namespace Universe

/--
The intersection of universes is a universe, with ambient space the
intersection of the ambient spaces.
-/
theorem iInter {ι : Sort*} (IsAmbient A : ι → G → Prop)
    [∀ i, Universe (IsAmbient i) (A i)] :
    Universe (fun g => ∀ i, IsAmbient i g) (fun g => ∀ i, A i g) where
  closed_sum g h hg hh i :=
    ClosedUnderSum.closed_sum g h (hg i) (hh i)
  has_option hg h i :=
    Hereditary.has_option (hg i) h
  neg_of hg i :=
    ClosedUnderNeg.neg_of (hg i)
  closed_dicotic B C _ _ hB hC hBne hCne hAmbient i :=
    ClosedUnderDicotic.closed_dicotic B C
      (fun b hb => hB b hb i) (fun c hc => hC c hc i) hBne hCne (hAmbient i)
  zero_mem i :=
    Universe.zero_mem (IsAmbient i) (A := A i)
  isAmbient_of_mem hg i :=
    Universe.isAmbient_of_mem (hg i)

-- TODO: construct a directed family of long universes whose union is not a
-- universe (i.e. justify this extra hypothesis)
/--
The union of a nonempty directed family of universes is a universe, with
ambient space the union of the ambient spaces.

The directedness is componentwise on the family of ordered pairs `(A i,
IsAmbient i)`. We require the hypothesis that, if the Left and Right options
lie in the union, and the form from dicotic closure lies in the union of the
ambient spaces, then there exists a universe containing all of the options, and
whose ambient space contains the relevant form.
-/
theorem iUnion_of_directed {ι : Sort*} [Nonempty ι] (IsAmbient A : ι → G → Prop)
    [∀ i, Universe (IsAmbient i) (A i)]
    (h_directed : Directed
      (r := fun P Q : (G → Prop) × (G → Prop) => P.1 ≤ Q.1 ∧ P.2 ≤ Q.2)
      (fun i => (A i, IsAmbient i)))
    (h_options : ∀ (B C : Set G) [Small B] [Small C],
      (∀ b ∈ B, ∃ i, A i b) → (∀ c ∈ C, ∃ i, A i c) →
      B.Nonempty → C.Nonempty → (∃ i, IsAmbient i (!{B | C} : G)) →
      ∃ i, (∀ b ∈ B, A i b) ∧ (∀ c ∈ C, A i c) ∧ IsAmbient i (!{B | C} : G)) :
    Universe (fun g => ∃ i, IsAmbient i g) (fun g => ∃ i, A i g) where
  closed_sum g h hg hh := by
    obtain ⟨i, hi⟩ := hg
    obtain ⟨j, hj⟩ := hh
    obtain ⟨k, hik, hjk⟩ := h_directed i j
    exact ⟨k, ClosedUnderSum.closed_sum g h (hik.1 g hi) (hjk.1 h hj)⟩
  has_option hg h := by
    obtain ⟨i, hi⟩ := hg
    exact ⟨i, Hereditary.has_option hi h⟩
  neg_of hg := by
    obtain ⟨i, hi⟩ := hg
    exact ⟨i, ClosedUnderNeg.neg_of hi⟩
  closed_dicotic B C _ _ hB hC hBne hCne hAmbient := by
    obtain ⟨i, hBi, hCi, hAmbienti⟩ := h_options B C hB hC hBne hCne hAmbient
    exact ⟨i, ClosedUnderDicotic.closed_dicotic B C hBi hCi hBne hCne hAmbienti⟩
  zero_mem := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, Universe.zero_mem (IsAmbient i) (A := A i)⟩
  isAmbient_of_mem hg := by
    obtain ⟨i, hi⟩ := hg
    exact ⟨i, Universe.isAmbient_of_mem hi⟩

/--
A specialised version of `Universe.iUnion_of_directed` in which every universe
has the same ambient space.
-/
theorem iUnion_of_directed_of_fixed_ambient {ι : Sort*} [Nonempty ι]
    (IsAmbient : G → Prop) (A : ι → G → Prop) [∀ i, Universe IsAmbient (A i)]
    (h_directed : Directed (r := (· ≤ ·)) A)
    (h_options : ∀ (B C : Set G) [Small B] [Small C],
      (∀ b ∈ B, ∃ i, A i b) → (∀ c ∈ C, ∃ i, A i c) →
      B.Nonempty → C.Nonempty → IsAmbient (!{B | C} : G) →
      ∃ i, (∀ b ∈ B, A i b) ∧ (∀ c ∈ C, A i c)) :
    Universe IsAmbient (fun g => ∃ i, A i g) where
  closed_sum g h hg hh := by
    obtain ⟨i, hi⟩ := hg
    obtain ⟨j, hj⟩ := hh
    obtain ⟨k, hik, hjk⟩ := h_directed i j
    exact ⟨k, ClosedUnderSum.closed_sum g h (hik g hi) (hjk h hj)⟩
  has_option hg h := by
    obtain ⟨i, hi⟩ := hg
    exact ⟨i, Hereditary.has_option hi h⟩
  neg_of hg := by
    obtain ⟨i, hi⟩ := hg
    exact ⟨i, ClosedUnderNeg.neg_of hi⟩
  closed_dicotic B C _ _ hB hC hBne hCne hAmbient := by
    obtain ⟨i, hBi, hCi⟩ := h_options B C hB hC hBne hCne hAmbient
    exact ⟨i, ClosedUnderDicotic.closed_dicotic B C hBi hCi hBne hCne hAmbient⟩
  zero_mem := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, Universe.zero_mem IsAmbient (A := A i)⟩
  isAmbient_of_mem hg := by
    obtain ⟨i, hi⟩ := hg
    exact Universe.isAmbient_of_mem hi

omit [Form G] in
private theorem exists_directed_upper_of_finite {ι : Sort*} [Nonempty ι] (A : ι → G → Prop)
    (h_directed : Directed (r := (· ≤ ·)) A)
    {S : Set G} (hS : S.Finite) (h_mem : ∀ g ∈ S, ∃ i, A i g) :
    ∃ i, ∀ g ∈ S, A i g := by
  obtain ⟨T, ⟨i, rfl⟩, hST⟩ :=
    h_directed.directedOn_range.exists_mem_subset_of_finite_of_subset_sUnion
      (Set.range_nonempty A) hS (fun g hg => by
        obtain ⟨i, hi⟩ := h_mem g hg
        exact Set.mem_sUnion_of_mem hi (Set.mem_range_self i))
  exact ⟨i, hST⟩

end Universe

namespace ShortUniverse

/--
The union of a nonempty directed family of short universes is a short universe.
-/
theorem iUnion_of_directed {ι : Sort*} [Nonempty ι] (A : ι → G → Prop)
    [∀ i, ShortUniverse (A i)]
    (h_directed : Directed (r := (· ≤ ·)) A) :
    ShortUniverse (fun g => ∃ i, A i g) where
  toUniverse :=
    Universe.iUnion_of_directed_of_fixed_ambient IsShort A h_directed
      (fun B C _ _ hB hC _ _ hShort => by
        have hBfin : B.Finite := by
          simpa [Form.moves_ofSets] using Short.finite_moves Player.left hShort
        have hCfin : C.Finite := by
          simpa [Form.moves_ofSets] using Short.finite_moves Player.right hShort
        obtain ⟨i, hi⟩ := Universe.exists_directed_upper_of_finite A h_directed hBfin hB
        obtain ⟨j, hj⟩ := Universe.exists_directed_upper_of_finite A h_directed hCfin hC
        obtain ⟨k, hik, hjk⟩ := h_directed i j
        exact ⟨k, fun b hb => hik b (hi b hb), fun c hc => hjk c (hj c hc)⟩)

end ShortUniverse

namespace Form

namespace Maintenance

theorem of_subset (A : G → Prop) (B : G → Prop)
    (h_subset : ∀g, B g → A g) (g h : G) {p : Player}
    (h_maintenance_a : Maintenance A g h p) : Maintenance B g h p := by
  unfold Maintenance at h_maintenance_a ⊢
  cases p
  · simp at h_maintenance_a ⊢
    intro hl h_hl_mem
    apply Or.elim (h_maintenance_a hl h_hl_mem)
    · intro ⟨gl, h_gl, h_gl_ge_hl⟩
      apply Or.inl
      use gl
      apply And.intro h_gl
      exact misereGE_of_subset A h_subset gl hl h_gl_ge_hl
    · intro ⟨hlr, h_hlr, h_g_ge_hlr⟩
      apply Or.inr
      use hlr
      apply And.intro h_hlr
      exact misereGE_of_subset A h_subset g hlr h_g_ge_hlr
  · simp at h_maintenance_a ⊢
    intro hl h_hl_mem
    apply Or.elim (h_maintenance_a hl h_hl_mem)
    · intro ⟨hr, h_hr, h_hl_ge_hr⟩
      apply Or.inl
      use hr
      apply And.intro h_hr
      exact misereGE_of_subset A h_subset hl hr h_hl_ge_hr
    · intro ⟨grl, h_grl, h_grl_ge_h⟩
      apply Or.inr
      use grl
      apply And.intro h_grl
      exact misereGE_of_subset A h_subset grl h h_grl_ge_h

end Maintenance

end Form

