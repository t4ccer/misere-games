import CombinatorialGames.Mathlib.Neg
import CombinatorialGames.Mathlib.Small
import CombinatorialGames.Player
import CombinatorialGames.Outcome
import Mathlib.Algebra.Group.Pointwise.Set.Basic

universe u v

-- Implementation detail
def Form.IsOption' {G : Type v} (moves : Player → G → Set G) (x y : G) : Prop :=
   x ∈ ⋃ p, moves p y

class Form (G : Type v) where
  moves (p : Player) (x : G) : Set G
  isOption'_wf : WellFounded (Form.IsOption' moves)

-- We need to keep this separate even if all forms have a notion of Neg because game_wf
-- is useful when implementing negation
class FormNeg (G : Type v) extends Form G, InvolutiveNeg G where
  moves_neg (p : Player) (x : G) : moves p (-x) = Set.neg.neg (moves (-p) x)

namespace Form

variable {G : Type u} [g_form : Form G]

/-- `IsOption x y` means that `x` is either a left or a right move for `y`. -/
def IsOption (x y : G) : Prop := IsOption' g_form.moves x y

-- /-- The set of left moves of the game. -/
-- scoped notation:max g:max "ᴸ" => Form.moves Player.left g

-- /-- The set of right moves of the game. -/
-- scoped notation:max g:max "ᴿ" => Form.moves Player.right g

@[aesop simp]
lemma isOption_iff_mem_union {x y : G} :
    IsOption x y ↔ x ∈ Form.moves .left y ∪ Form.moves .right y := by
  simp [IsOption, IsOption', Player.exists]

theorem IsOption.of_mem_moves {x y : G} {p : Player} (h : x ∈ moves p y) :
    IsOption x y := ⟨_, ⟨p, rfl⟩, h⟩

instance (x : G) : Small.{u} {y // IsOption y x} :=
  inferInstanceAs (Small (⋃ p, Form.moves p x))

theorem isOption_wf : WellFounded (@IsOption G _) := g_form.isOption'_wf

instance : IsWellFounded _ (@IsOption G _) := ⟨isOption_wf⟩

theorem IsOption.irrefl (x : G) : ¬ IsOption x x := _root_.irrefl x

theorem self_notMem_moves (p : Player) (x : G) : x ∉ moves p x :=
  fun hx ↦ IsOption.irrefl x (.of_mem_moves hx)

/-- A (proper) subposition is any game in the transitive closure of `IsOption`. -/
def Subposition : G → G → Prop :=
  Relation.TransGen IsOption

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_moves {p} {x y : G} (h : x ∈ moves p y) : Subposition x y :=
  Relation.TransGen.single (.of_mem_moves h)

theorem Subposition.trans {x y z : G} (h₁ : Subposition x y) (h₂ : Subposition y z) :
    Subposition x z :=
  Relation.TransGen.trans h₁ h₂

instance (x : G) : Small.{u} {y // Subposition y x} :=
  small_transGen' _ x

instance : IsTrans _ (@Subposition G _) := inferInstanceAs (IsTrans _ (Relation.TransGen _))
instance : IsWellFounded _ (@Subposition G _) := inferInstanceAs (IsWellFounded _ (Relation.TransGen _))
instance : WellFoundedRelation G := ⟨Subposition, instIsWellFoundedSubposition.wf⟩

macro "form_wf" : tactic =>
  `(tactic| all_goals solve_by_elim (maxDepth := 8)
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subposition.of_mem_moves, Subposition.trans, Subtype.prop] )

end Form

namespace FormNeg

variable {G : Type u} [g_form : FormNeg G]

theorem exists_moves_neg {P : G → Prop} {p : Player} {x : G} :
    (∃ y ∈ Form.moves p (-x), P y) ↔ (∃ y ∈ Form.moves (-p) x, P (-y)) := by
  simp only [FormNeg.moves_neg, Set.mem_neg, Set.exists_mem_neg]

end FormNeg

class MisereForm (G : Type v) extends Form G where
  WinsGoingFirst (p : Player) (g : G) : Prop

namespace MisereForm

variable {G : Type u} [g_form : MisereForm G]

open scoped Classical in
noncomputable def MiserePlayerOutcome : G → Player → Player :=
  fun g p => if WinsGoingFirst p g then p else -p

open scoped Classical in
noncomputable def MisereOutcome : G → Outcome :=
  fun g => Outcome.ofPlayers (MiserePlayerOutcome g .left) (MiserePlayerOutcome g .right)

end MisereForm
