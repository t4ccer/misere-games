module

public import CombinatorialGames.Form.Short
public import CombinatorialGames.Misere.Hereditary

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open GameForm
open GameForm.Misere.Outcome

public section

class ClosedUnderSum (A : G → Prop) [Add G] where
  closed_sum (g h : G) (h1 : A g) (h2 : A h) : A (g + h)

class ClosedUnderFollower (A : G → Prop) where
  closed_follower (g : G) (h1 : A g) : ∀g', IsOption g' g → A g'

class ClosedUnderDicotic (A : GameForm → Prop) where
  closed_dicotic (B C : Set GameForm) (hB : ∀ b ∈ B, A b) (hC : ∀ c ∈ C, A c)
    [Small B] [Small C] : A !{B | C}

class ClosedUnderDicoticShort (A : GameForm → Prop) where
  closed_dicotic_short (B C : Set GameForm) (hB : ∀ b ∈ B, A b) (hC : ∀ c ∈ C, A c)
    (hBfin : B.Finite) (HBnonempty : B.Nonempty)
    (hCfin : C.Finite) (HCnonempty : C.Nonempty) [Small B] [Small C] : A !{B | C}

class ShortUniverse (A : GameForm → Prop) extends
  ClosedUnderSum A, ClosedUnderFollower A,
  ClosedUnderNeg A, ClosedUnderDicoticShort A where
  short_only (g : GameForm) (h1 : A g) : Short g

namespace GameForm

theorem Maintenance_of_subset (U : GameForm → Prop) (pfU : GameForm → Prop)
    (h_subset : ∀g, pfU g → U g) (g h : GameForm) {p : Player}
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
      exact MisereGe_of_subset U h_subset gl hl h_gl_ge_hl
    · intro ⟨hlr, h_hlr, h_g_ge_hlr⟩
      apply Or.inr
      use hlr
      apply And.intro h_hlr
      exact MisereGe_of_subset U h_subset g hlr h_g_ge_hlr
  · simp at h_maintenance_u ⊢
    intro hl h_hl_mem
    apply Or.elim (h_maintenance_u hl h_hl_mem)
    · intro ⟨hr, h_hr, h_hl_ge_hr⟩
      apply Or.inl
      use hr
      apply And.intro h_hr
      exact MisereGe_of_subset U h_subset hl hr h_hl_ge_hr
    · intro ⟨grl, h_grl, h_grl_ge_h⟩
      apply Or.inr
      use grl
      apply And.intro h_grl
      exact MisereGe_of_subset U h_subset grl h h_grl_ge_h

theorem misere_ge_iff_maintenance_and_proviso {U : GameForm → Prop} [ShortUniverse U]
    (g h : GameForm) :
    g ≥m U h ↔ Maintenance U g h .right ∧ Maintenance U g h .left ∧
               Proviso U g h .right ∧ Proviso U h g .left := by
  sorry

end GameForm
