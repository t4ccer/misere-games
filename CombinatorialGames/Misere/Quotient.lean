/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Form.Misere.Outcome
public import CombinatorialGames.GameForm
public import CombinatorialGames.Form.Classes

public noncomputable section

open Form
open Form.Misere.Outcome

universe u

variable {G : Type (u + 1)} [Form G]

@[expose] def MisereSetoid (A : G → Prop) : Setoid {g : G // A g} :=
  ⟨ fun g h => MisereEQ A g h
  , fun _ ↦ MisereEQ.symm fun _ ↦ congrFun rfl
  , MisereEQ.symm
  , MisereEQ.trans
  ⟩

@[expose] def MisereQuotient (A : G → Prop) := Quotient (MisereSetoid A)

namespace Form.MisereQuotient

@[expose] def mk (A : G → Prop) (x : G) (h1 : A x) : MisereQuotient A := Quotient.mk (MisereSetoid A) ⟨x, h1⟩

@[no_expose] def out {A : G → Prop} (x : MisereQuotient (A := A)) : {g : G // A g} := Quotient.out x

variable {A : G → Prop}

instance : PartialOrder (MisereQuotient (A := A)) where
  le g h := h.out ≥m A g.out
  le_refl g := MisereGE.refl (g.out : G)
  le_trans g h k h1 h2 := MisereGE.trans h2 h1
  le_antisymm g h:= Quotient.inductionOn₂' g h fun x y h1 h2 => by
    apply Quotient.sound'
    have h3 := Quotient.mk_out (s := MisereSetoid A) x
    have h4 := Quotient.mk_out (s := MisereSetoid A) y
    exact MisereEq.of_antisymm
      (misereGE_rw_left h3 (misereGE_rw_right (MisereEQ.symm h4) h2))
      (misereGE_rw_left h4 (misereGE_rw_right (MisereEQ.symm h3) h1))

theorem mk_eq_mk {x y : G} {hx : A x} {hy : A y} : mk A x hx = mk A y hy ↔ x =m A y := Quotient.eq

theorem mk_out_equiv (x : G) {hx : A x} : (mk A x hx).out =m A x :=
    Quotient.mk_out (s := MisereSetoid A) ⟨x, hx⟩

theorem self_misereEQ_mk_out (g : G) (hx : A g) : g =m A(mk A g hx).out :=
  MisereEQ.symm (mk_out_equiv g)

end Form.MisereQuotient

namespace GameForm.MisereQuotient

open Form.MisereQuotient

variable {A : GameForm → Prop}

noncomputable instance [Hereditary A] [ClosedUnderAdd A] : Add (MisereQuotient A) :=
  ⟨Quotient.map₂'
    (fun g h => ⟨(g : GameForm) + (h : GameForm), ClosedUnderAdd.has_add (G := GameForm) g h g.prop h.prop⟩)
    (by
      intro x y h1 z w h2
      show (↑x + ↑z) =m A (↑y + ↑w)
      intro t ht
      have hzt : A (↑z + t) := ClosedUnderAdd.has_add _ _ z.prop ht
      have hty : A (t + ↑y) := ClosedUnderAdd.has_add _ _ ht y.prop
      calc MisereOutcome ((↑x + ↑z) + t)
          = MisereOutcome (↑x + (↑z + t)) := by rw [add_assoc]
        _ = MisereOutcome (↑y + (↑z + t)) := h1 (↑z + t) hzt
        _ = MisereOutcome ((↑z + t) + ↑y) := by rw [add_comm]
        _ = MisereOutcome (↑z + (t + ↑y)) := by rw [add_assoc]
        _ = MisereOutcome (↑w + (t + ↑y)) := h2 (t + ↑y) hty
        _ = MisereOutcome ((↑w + t) + ↑y) := by rw [← add_assoc]
        _ = MisereOutcome (↑y + (↑w + t)) := by rw [add_comm]
        _ = MisereOutcome ((↑y + ↑w) + t) := by rw [add_assoc]
    )
⟩

end GameForm.MisereQuotient
