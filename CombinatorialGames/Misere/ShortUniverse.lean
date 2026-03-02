module

public import CombinatorialGames.GameForm.Misere.Outcome

universe u

variable {G : Type (u + 1)} [Form G]

open Form
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
    (hBfin : B.Finite) (hCfin : C.Finite) [Small B] [Small C] : A !{B | C}

class ShortUniverse (A : GameForm → Prop) extends
  ClosedUnderSum A, ClosedUnderFollower A,
  ClosedUnderNeg A, ClosedUnderDicoticShort A where
  short_only (g : GameForm) (h1 : A g) : Form.Short g

namespace GameForm

@[expose] def Strong (U : GameForm → Prop) (g : GameForm) (p : Player) : Prop :=
  ∀ x, U x → IsEnd p x → MisereForm.WinsGoingFirst p (g + x)

@[expose] def Maintenance (U : GameForm → Prop) (g h : GameForm) (p : Player) : Prop :=
  match p with
  | .right => ∀ gr ∈ moves .right g,
      (∃ hr ∈ moves .right h, gr ≥m U hr) ∨
      (∃ grl ∈ moves .left gr, grl ≥m U h)
  | .left => ∀ hl ∈ moves .left h,
      (∃ gl ∈ moves .left g, gl ≥m U hl) ∨
      (∃ hlr ∈ moves .right hl, g ≥m U hlr)

@[expose] def Proviso (U : GameForm → Prop) (g h : GameForm) (p : Player) : Prop :=
  IsEnd p g → Strong U h p

theorem misere_ge_iff_maintenance_and_proviso {U : GameForm → Prop} [ShortUniverse U]
    (g h : GameForm) :
    g ≥m U h ↔ Maintenance U g h .right ∧ Maintenance U g h .left ∧
               Proviso U g h .right ∧ Proviso U h g .left := by
  sorry

end GameForm
