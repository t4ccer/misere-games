module

public import CombinatorialGames.AugmentedForm
public import CombinatorialGames.AugmentedForm.Misere.Outcome
public import CombinatorialGames.Form
public import CombinatorialGames.Form.Misere.Outcome
public import CombinatorialGames.GameForm.Misere.Outcome
public import CombinatorialGames.Misere.DeadEnding
public import CombinatorialGames.Misere.ShortUniverse

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open GameForm.Misere.Outcome

public section

namespace GameForm

def IsBlockedEnd (g : GameForm) (p : Player) : Prop :=
  (IsEnd p g)
    ∧ (∀ gr ∈ moves (-p) g,
         (gr.IsBlockedEnd p
         ∨ (∃ grl,∃ (_ : grl ∈ moves p gr), grl.IsBlockedEnd p)))
termination_by g
decreasing_by all_goals form_wf

def IsBlocking (g : GameForm) : Prop :=
  (∀ p, IsEnd p g → g.IsBlockedEnd p) ∧ (∀ p, ∀gp ∈ moves p g, gp.IsBlocking)
termination_by g
decreasing_by form_wf

def Augmented_strong (U : GameForm → Prop) (g : AugmentedForm) (p : Player) : Prop :=
  ∀ x, U x → IsEndLike p x → MisereForm.WinsGoingFirst p (g + (x : AugmentedForm))

def AugmentedMisereGe (U : GameForm → Prop) (g h : AugmentedForm) : Prop :=
  ∀ x, (U x → MisereForm.MisereOutcome (g + (x : AugmentedForm)) ≥ MisereForm.MisereOutcome (h + (x : AugmentedForm)))

/-- `G ≥ma U H` means that G ≥_U H for AugmentedForms -/
macro_rules | `($x ≥ma $u $y) => `(AugmentedMisereGe $u $x $y)

def Augmented_maintenance (U : GameForm → Prop) (g h : AugmentedForm) (p : Player) : Prop :=
  match p with
  | .right => ∀ gr ∈ moves .right g,
      (∃ hr ∈ moves .right h, gr ≥ma U hr) ∨
      (∃ grl ∈ moves .left gr, grl ≥ma U h)
  | .left => ∀ hl ∈ moves .left h,
      (∃ gl ∈ moves .left g, gl ≥ma U hl) ∨
      (∃ hlr ∈ moves .right hl, g ≥ma U hlr)

def Augmented_proviso (U : GameForm → Prop) (g h : AugmentedForm) (p : Player) : Prop :=
  IsEndLike p g →  Augmented_strong U h p

lemma ofGameForm_preserves_short (g : GameForm) [Form.Short g] :
    Form.Short (AugmentedForm.ofGameForm g) := by
  sorry

lemma toGameForm_preserves_short (g : AugmentedForm) [Form.Short g] (h : AugmentedForm.TombstoneFree g) :
    Form.Short (AugmentedForm.toGameForm g h) := by
  sorry

lemma winsGoingFirst_coercion_compat (g : GameForm) (p : Player) :
    MisereForm.WinsGoingFirst p g ↔ MisereForm.WinsGoingFirst p (g : AugmentedForm) := by
  sorry

lemma misereOutcome_coercion_compat (g : GameForm) :
    MisereForm.MisereOutcome g = MisereForm.MisereOutcome (g : AugmentedForm) := by
  simp only [MisereForm.MisereOutcome, MisereForm.MiserePlayerOutcome]
  congr 2 <;> simp [winsGoingFirst_coercion_compat]

-- can just replace with ofGameForms_moves_mem_iff
lemma moves_coercion_compat (g : GameForm) (p : Player) (x : GameForm) :
    x ∈ moves p g ↔ (x : AugmentedForm) ∈ moves p (g : AugmentedForm) := by
  exact AugmentedForm.ofGameForm_moves_mem_iff.symm

lemma moves_empty_coercion_compat (g : GameForm) (p : Player) :
    moves p g = ∅ ↔ moves p (g : AugmentedForm) = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h ap hap
    have ⟨gp, hgp, heq⟩ := AugmentedForm.mem_moves_ofGameForm hap
    rw [← heq] at hap
    have : gp ∈ moves p g := AugmentedForm.ofGameForm_moves_mem_iff.mp hap
    exact h gp this
  · intro h gp hgp
    have : (gp : AugmentedForm) ∈ moves p (g : AugmentedForm) :=
      AugmentedForm.ofGameForm_moves_mem_iff.mpr hgp
    exact h (gp : AugmentedForm) this

lemma isEnd_coercion_compat (g : GameForm) (p : Player) :
    IsEnd p g ↔ IsEndLike p (g : AugmentedForm) := by
  simp only [IsEnd_def, AugmentedForm.IsEndLike_iff]
  constructor
  · intro h
    right
    exact (moves_empty_coercion_compat g p).mp h
  · intro h
    cases h with
    | inl h1 =>
      exfalso
      have : ¬AugmentedForm.hasTombstone p (g : AugmentedForm) :=
        AugmentedForm.not_hasTombstone_ofGameForm g p
      exact this h1
    | inr h2 =>
      exact (moves_empty_coercion_compat g p).mpr h2

lemma strong_coercion_compat {U : GameForm → Prop} (g : GameForm) (p : Player) :
    Strong U g p ↔ Augmented_strong U (g : AugmentedForm) p := by
  simp only [Strong, Augmented_strong]
  constructor
  · intro h x hx h_end
    rw [GameForm.IsEndLike_iff, <-AugmentedForm.IsEndLike_ofGameForm_iff] at h_end
    have h_end' := (isEnd_coercion_compat x p).mpr h_end
    have h1 := h x hx h_end'
    convert (winsGoingFirst_coercion_compat (g + x) p).mp h1 using 1
    rw [AugmentedForm.ofGameForm_add]
  · intro h x hx h_end
    have h_end' := (isEnd_coercion_compat x p).mp h_end
    rw [AugmentedForm.IsEndLike_ofGameForm_iff, <-GameForm.IsEndLike_iff] at h_end'
    have h1 := h x hx h_end'
    have h2 : MisereForm.WinsGoingFirst p (AugmentedForm.ofGameForm (g + x)) := by
      convert h1 using 1
      rw [AugmentedForm.ofGameForm_add]
    exact (winsGoingFirst_coercion_compat (g + x) p).mpr h2

lemma misere_ge_coercion_compat {U : GameForm → Prop} (g h : GameForm) :
    g ≥m U h ↔ (g : AugmentedForm) ≥ma U (h : AugmentedForm) := by
  simp only [GameForm.Misere.Outcome.MisereGe, AugmentedMisereGe]
  constructor
  · intro h1 x hx
    have h2 := h1 x hx
    rw [misereOutcome_coercion_compat (g + x), misereOutcome_coercion_compat (h + x)] at h2
    rwa [AugmentedForm.ofGameForm_add, AugmentedForm.ofGameForm_add] at h2
  · intro h1 x hx
    have h2 := h1 x hx
    rw [← AugmentedForm.ofGameForm_add, ← AugmentedForm.ofGameForm_add] at h2
    rwa [← misereOutcome_coercion_compat (g + x), ← misereOutcome_coercion_compat (h + x)] at h2

lemma maintenance_coercion_compat {U : GameForm → Prop} (g h : GameForm) (p : Player) :
    Maintenance U g h p ↔ Augmented_maintenance U (g : AugmentedForm) (h : AugmentedForm) p := by
  sorry

lemma proviso_coercion_compat {U : GameForm → Prop} (g h : GameForm) (p : Player) :
    Proviso U g h p ↔ Augmented_proviso U (g : AugmentedForm) (h : AugmentedForm) p := by
  simp only [Proviso, Augmented_proviso, isEnd_coercion_compat, strong_coercion_compat]

theorem augmented_misere_ge_iff_maintenance_and_proviso {U : GameForm → Prop} [ShortUniverse U]
    (g h : AugmentedForm) [Form.Short g] [Form.Short h] :
    g ≥ma U h ↔ Augmented_maintenance U g h .right ∧ Augmented_maintenance U g h .left ∧
                Augmented_proviso U g h .right ∧ Augmented_proviso U h g .left := by
  sorry

theorem misere_ge_iff_maintenance_and_proviso' {U : GameForm → Prop} [ShortUniverse U]
    (g h : GameForm) [Form.Short g] [Form.Short h] :
    g ≥m U h ↔ Maintenance U g h .right ∧ Maintenance U g h .left ∧
               Proviso U g h .right ∧ Proviso U h g .left := by
  have hgs : Form.Short (g : AugmentedForm) := ofGameForm_preserves_short g
  have hhs : Form.Short (h : AugmentedForm) := ofGameForm_preserves_short h
  rw [misere_ge_coercion_compat, augmented_misere_ge_iff_maintenance_and_proviso,
      maintenance_coercion_compat, maintenance_coercion_compat,
      proviso_coercion_compat, proviso_coercion_compat]

def invertible (U : GameForm → Prop) (g : GameForm) : Prop :=
  ∃ h, U h ∧ (g + h) =m U 0

-- Conjugate property
theorem self_sub_eq_zero_iff_invertible {U : GameForm → Prop} [ShortUniverse U]
    (g : GameForm) (hg : U g) :
    (g - g) =m U 0 ↔ invertible U g := by
  sorry

class NoP (A : GameForm → Prop) where
  no_P (g : GameForm) (h1 : A g) : MisereForm.MisereOutcome g ≠ .P

class DeadEnding (A : GameForm → Prop) where
  dead_ending (g : GameForm) : IsDeadEnding g

theorem theorem4 {A : GameForm → Prop} [ClosedUnderNeg A] [ClosedUnderSum A]
    [ClosedUnderFollower A] [DeadEnding A] [NoP A] (g : GameForm) (h1 : A g) :
    (g + (-g)) =m A 0 := by
  sorry

end GameForm
