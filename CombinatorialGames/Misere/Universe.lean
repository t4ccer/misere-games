/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import CombinatorialGames.Form.Short
public import CombinatorialGames.Misere.Hereditary

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Form.Misere.Outcome

public section

class ClosedUnderSum (A : G → Prop) [Add G] where
  closed_sum (g h : G) (h1 : A g) (h2 : A h) : A (g + h)

class ClosedUnderDicotic (IsAmbient : G → Prop) (A : G → Prop) where
  closed_dicotic (B C : Set G) [Small B] [Small C]
      (hB : ∀ b ∈ B, A b) (hC : ∀ c ∈ C, A c) :
    B.Nonempty → C.Nonempty → IsAmbient (!{B | C} : G) → A (!{B | C} : G)

abbrev ClosedUnderLongDicotic (A : G → Prop) :=
  ClosedUnderDicotic (fun _ => True) A

abbrev ClosedUnderShortDicotic (A : G → Prop) :=
  ClosedUnderDicotic IsShort A

class Universe (IsAmbient : G → Prop) (A : G → Prop) extends
    ClosedUnderSum A, Hereditary A, ClosedUnderNeg A, ClosedUnderDicotic IsAmbient A where
  zero_mem : A 0
  isAmbient_of_mem {g : G} : A g → IsAmbient g

class LongUniverse (A : G → Prop) extends Universe (fun _ => True) A

class ShortUniverse (A : G → Prop) extends Universe IsShort A

namespace Form

theorem Maintenance_of_subset (U : G → Prop) (pfU : G → Prop)
    (h_subset : ∀g, pfU g → U g) (g h : G) {p : Player}
    (h_maintenance_u : Maintenance U g h p) : Maintenance pfU g h p := by
  unfold Maintenance at h_maintenance_u ⊢
  cases p
  · simp at h_maintenance_u ⊢
    intro hl h_hl_mem
    apply Or.elim (h_maintenance_u hl h_hl_mem)
    · intro ⟨gl, h_gl, h_gl_ge_hl⟩
      apply Or.inl
      use gl
      apply And.intro h_gl
      exact misereGE_of_subset U h_subset gl hl h_gl_ge_hl
    · intro ⟨hlr, h_hlr, h_g_ge_hlr⟩
      apply Or.inr
      use hlr
      apply And.intro h_hlr
      exact misereGE_of_subset U h_subset g hlr h_g_ge_hlr
  · simp at h_maintenance_u ⊢
    intro hl h_hl_mem
    apply Or.elim (h_maintenance_u hl h_hl_mem)
    · intro ⟨hr, h_hr, h_hl_ge_hr⟩
      apply Or.inl
      use hr
      apply And.intro h_hr
      exact misereGE_of_subset U h_subset hl hr h_hl_ge_hr
    · intro ⟨grl, h_grl, h_grl_ge_h⟩
      apply Or.inr
      use grl
      apply And.intro h_grl
      exact misereGE_of_subset U h_subset grl h h_grl_ge_h

end Form
