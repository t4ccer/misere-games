module

public import CombinatorialGames.Form.Misere.Outcome
public import CombinatorialGames.GameForm
public import CombinatorialGames.Misere.Hereditary

public noncomputable section

open Form
open Form.Misere.Outcome

universe u

variable {G : Type (u + 1)} [Form G]

def MisereSetoid (A : G → Prop) : Setoid {g : G // A g} :=
  ⟨ fun g h => MisereEq A g h
  , fun _ ↦ MisereEq_symm fun _ ↦ congrFun rfl
  , MisereEq_symm
  , MisereEq_trans
  ⟩

@[expose] def MisereQuotient (A : G → Prop) := Quotient (MisereSetoid A)

namespace Form.MisereQuotient

def mk (A : G → Prop) (x : G) (h1 : A x) : MisereQuotient A := Quotient.mk (MisereSetoid A) ⟨x, h1⟩

@[no_expose] def out {A : G → Prop} (x : MisereQuotient (A := A)) : {g : G // A g} := Quotient.out x

variable {A : G → Prop}

instance : PartialOrder (MisereQuotient (A := A)) where
  le g h := h.out ≥m A g.out
  le_refl g := MisereGe_refl (g.out : G)
  le_trans g h k h1 h2 := MisereGe_trans h2 h1
  le_antisymm g h:= Quotient.inductionOn₂' g h fun x y h1 h2 => by
    apply Quotient.sound'
    have h3 := Quotient.mk_out (s := MisereSetoid A) x
    have h4 := Quotient.mk_out (s := MisereSetoid A) y
    exact MisereGe_antisymm
      (MisereGe_rw_left h3 (MisereGe_rw_right (MisereEq_symm h4) h2))
      (MisereGe_rw_left h4 (MisereGe_rw_right (MisereEq_symm h3) h1))

theorem mk_eq_mk {x y : G} {hx : A x} {hy : A y} : mk A x hx = mk A y hy ↔ x =m A y := Quotient.eq

theorem mk_out_equiv (x : G) {hx : A x} : (mk A x hx).out =m A x :=
    Quotient.mk_out (s := MisereSetoid A) ⟨x, hx⟩

theorem self_MisereEq_mk_out (g : G) (hx : A g) : g =m A(mk A g hx).out :=
  MisereEq_symm (mk_out_equiv g)

end Form.MisereQuotient

namespace GameForm.MisereQuotient

open Form.MisereQuotient

variable {A : GameForm → Prop}

-- theorem mk_ofSets' [Hereditary A] (st : Player → Set GameForm)
--     [Small.{u} (st .left)] [Small.{u} (st .right)]
--     : mk A !{st} = !{fun p ↦ mk A '' st p} := by
--   refine mk_eq_mk.mpr <| ?_
--   simp [Set.image]
--   apply Hereditary.MisereEq_of_moves
--   · simp only [moves_ofSets, Set.mem_setOf_eq, exists_exists_and_eq_and]
--     intro gl h1
--     use gl, h1, self_MisereEq_mk_out gl
--   · simp only [moves_ofSets, Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
--     intro gl h1
--     use gl, h1, MisereEq_symm (self_MisereEq_mk_out gl)
--   · simp only [moves_ofSets, Set.mem_setOf_eq, exists_exists_and_eq_and]
--     intro gr h1
--     use gr, h1, self_MisereEq_mk_out gr
--   · simp only [moves_ofSets, Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
--     intro gr h1
--     use gr, h1, MisereEq_symm (self_MisereEq_mk_out gr)

-- @[simp]
-- theorem mk_ofSets {A : GameForm → Prop} [Hereditary A]
--     (s t : Set GameForm) [Small.{u} s] [Small.{u} t]
--     : mk A !{s | t} = !{mk A '' s | mk A '' t} := by
--   rw [mk_ofSets']
--   simp_rw [Player.apply_cases]

-- instance : Zero (MisereQuotient A) := ⟨mk A 0⟩
-- instance : One (MisereQuotient A) := ⟨mk A 1⟩

class ClosedUnderAdd (A : GameForm → Prop) where
  closed_add {g h : GameForm} (hg : A g) (hh : A h) : A (g + h)

instance [ClosedUnderAdd A] : Add (MisereQuotient A) :=  ⟨Quotient.map₂' (fun g h => ⟨(g : GameForm) + (h : GameForm), ClosedUnderAdd.closed_add g.prop h.prop⟩) (by
  intro x y h1 z w h2
  dsimp only
  obtain h1 : x =m A y := h1
  obtain h2 : z =m A w := h2
  have h3 : (x + z) =m A (y + w) := by 
    refine Hereditary.MisereEq_of_moves ?_ ?_ ?_ ?_
    · intro xz_l h4
      simp at h4
      obtain ⟨xl, h4, h5⟩ | h4 := h4
      · use xl + w
        constructor
        · refine add_right_mem_moves_add ?_ w
          
          sorry
        · sorry
      · sorry
    · sorry
    · sorry
    · sorry
  exact h3
  )⟩

-- instance : AddCommGroupWithOne (MisereQuotient A) where
--   zero_add := by rintro ⟨x⟩; exact congr(mk A $(zero_add _))
--   add_zero := by rintro ⟨x⟩; exact congr(mk A $(add_zero _))
--   add_comm := by rintro ⟨x⟩ ⟨y⟩; exact congr(mk A $(add_comm _ _))
--   add_assoc := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact congr(mk A $(add_assoc _ _ _))
--   neg_add_cancel := by rintro ⟨a⟩; exact mk_eq (neg_add_equiv _)
--   nsmul := nsmulRec
--   zsmul := zsmulRec

end GameForm.MisereQuotient
