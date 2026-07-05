/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.AugmentedForm.Short
public import CombinatorialGames.Misere.Universe

public section

open AugmentedForm
open Form
open Form.Misere.Outcome

universe u

/--
Lift set of `GameForm`s into a set of `AugmenteForm`s with the same elements
-/
@[expose] def AugmentedSet (A : GameForm → Prop) : AugmentedForm → Prop :=
  fun a => ∃ x, A x ∧ a = ofGameForm x

theorem misereEQ_ofGameForm_iff {A : GameForm → Prop} {g h : GameForm} :
    (ofGameForm g) =m (AugmentedSet A) (ofGameForm h) ↔ g =m A h := by
  constructor
  · intro h1 x hx
    have := h1 (ofGameForm x) ⟨x, hx, rfl⟩
    rwa [←ofGameForm_add, ←ofGameForm_add,
         misereOutcome_ofGameForm, misereOutcome_ofGameForm] at this
  · rintro h1 a ⟨x, hx, rfl⟩
    rw [←ofGameForm_add, ←ofGameForm_add,
        misereOutcome_ofGameForm, misereOutcome_ofGameForm]
    exact h1 x hx

theorem ofGameForm_ofSets (st : Player → Set GameForm)
    [Small (st .left)] [Small (st .right)] :
    ofGameForm !{st} = !{fun p => ofGameForm '' (st p)} := by
  apply AugmentedForm.ext
  · intro p
    ext x
    rw [Form.moves_ofSets]
    constructor
    · intro hx
      obtain ⟨gp, hgp, rfl⟩ := mem_moves_ofGameForm hx
      rw [Form.moves_ofSets] at hgp
      exact Set.mem_image_of_mem _ hgp
    · intro hx
      obtain ⟨gp, hgp, rfl⟩ := hx
      apply ofGameForm_moves_mem_iff.mpr
      rw [Form.moves_ofSets]
      exact hgp
  · intro p
    constructor
    · intro h; exact absurd h (not_hasTombstone_ofGameForm _ _)
    · intro h; exact absurd h (hasTombstone_ofSets _ _)

theorem ofGameForm_dicotic (B' C' : Set GameForm) [Small B'] [Small C'] :
    ofGameForm !{B' | C'} = !{ofGameForm '' B' | ofGameForm '' C'} := by
  convert ofGameForm_ofSets ( fun p => p.casesOn B' C' )
  · rename_i p; cases p <;> rfl
  · cases ‹Player› <;> rfl

variable {U : GameForm → Prop}

instance [ClosedUnderAdd U] : ClosedUnderAdd (AugmentedSet U) where
  has_add := by
    rintro g h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    use x + y
    simp [ofGameForm_add, *]
    convert (ClosedUnderAdd.has_add x y hx hy) using 1

instance [Hereditary U] : Hereditary (AugmentedSet U) where
  has_option := by
    rintro g g' ⟨x, hx, rfl⟩ ⟨p, ⟨⟨q, rfl⟩, hp⟩⟩
    obtain ⟨y, hy, rfl⟩ := mem_moves_ofGameForm hp
    exact ⟨y, Hereditary.of_mem_moves hx hy, rfl⟩

instance [ClosedUnderNeg U] : ClosedUnderNeg (AugmentedSet U) where
  neg_of := by
    rintro g ⟨x, hx, rfl⟩
    use -x
    simp [hx, ofGameForm_neg]

instance [ClosedUnderDicotic IsShort U] :
    ClosedUnderDicotic IsShort (AugmentedSet U) where
  closed_dicotic := by
    intros B C _ _ hB hC hB_nonempty hC_nonempty h_short
    obtain ⟨B', hB', hB_eq⟩ : ∃ B' : Set GameForm, B = ofGameForm '' B' ∧ (∀ b ∈ B', U b) := by
      refine ⟨{x : GameForm | ∃ b ∈ B, ofGameForm x = b},
        Set.ext fun b => ⟨fun hb => ?_, fun hb => ?_⟩, fun x hx => ?_⟩
      · obtain ⟨x, hAx, rfl⟩ := hB b hb
        exact ⟨x, ⟨ofGameForm x, hb, rfl⟩, rfl⟩
      · obtain ⟨x, hxB', rfl⟩ := hb
        obtain ⟨c, hc, hxc⟩ := hxB'
        rwa [hxc]
      · obtain ⟨c, hc, hxc⟩ := hx
        obtain ⟨y, hAy, hcy⟩ := hB c hc
        have hxy : x = y := ofGameForm_Injective (by rw [hxc, hcy])
        rwa [hxy]
    obtain ⟨C', hC', hC_eq⟩ : ∃ C' : Set GameForm, C = ofGameForm '' C' ∧ (∀ c ∈ C', U c) := by
      refine ⟨{c : GameForm | ofGameForm c ∈ C},
        Set.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩, fun c hc => ?_⟩
      · obtain ⟨x, hAx, rfl⟩ := hC y hy
        exact ⟨x, hy, rfl⟩
      · obtain ⟨c, hcC', rfl⟩ := hy
        exact hcC'
      · obtain ⟨x, hAx, hcx⟩ := hC (ofGameForm c) hc
        have hcx2 : c = x := ofGameForm_Injective hcx
        rwa [hcx2]
    haveI hsB : Small B' :=
      small_of_injective (show Function.Injective (fun x : B' => (⟨ofGameForm x, by
          rw [hB']; exact Set.mem_image_of_mem _ x.2⟩ : B)) from
        fun x y hxy => by simpa [Subtype.ext_iff] using
          ofGameForm_Injective (by simpa [Subtype.ext_iff] using hxy))
    haveI hsC : Small C' :=
      small_of_injective (show Function.Injective (fun x : C' => (⟨ofGameForm x, by
          rw [hC']; exact Set.mem_image_of_mem _ x.2⟩ : C)) from
        fun x y hxy => by simpa [Subtype.ext_iff] using
          ofGameForm_Injective (by simpa [Subtype.ext_iff] using hxy))
    have heq : (!{B | C} : AugmentedForm) = ofGameForm !{B' | C'} := by
      subst hB' hC'; exact (ofGameForm_dicotic B' C').symm
    have hshortBC' : IsShort (!{B' | C'} : GameForm) :=
      isShort_ofGameForm_iff.mp (heq ▸ h_short)
    have hBne : B'.Nonempty := by
      obtain ⟨b, hb⟩ := hB_nonempty; rw [hB'] at hb
      obtain ⟨x, hx, _⟩ := hb; exact ⟨x, hx⟩
    have hCne : C'.Nonempty := by
      obtain ⟨c, hc⟩ := hC_nonempty; rw [hC'] at hc
      obtain ⟨x, hx, _⟩ := hc; exact ⟨x, hx⟩
    exact ⟨!{B' | C'},
      ClosedUnderDicotic.closed_dicotic B' C' hB_eq hC_eq hBne hCne hshortBC', heq⟩

instance [ShortUniverse U] : ShortUniverse (AugmentedSet U) where
  zero_mem := by
    use 0; simp [ofGameForm_zero]
    exact ‹ShortUniverse U›.zero_mem
  isAmbient_of_mem := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact isShort_ofGameForm_iff.mpr (‹ShortUniverse U›.isAmbient_of_mem hx)
