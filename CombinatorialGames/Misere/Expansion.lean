/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.SimplestForm
public import CombinatorialGames.AugmentedForm.Short

public section

open AugmentedForm
open Form
open Form.Misere.Outcome

universe u

-- TODO: Rename to AugmentedSet, also move somewhere else

/--
The image predicate of a `GameForm` predicate under `ofGameForm`.
-/
@[expose] def imagePred (A : GameForm.{u} → Prop) : AugmentedForm.{u} → Prop :=
  fun a => ∃ x, A x ∧ a = ofGameForm x

theorem misereEQ_ofGameForm_iff {A : GameForm.{u} → Prop} {g h : GameForm.{u}} :
    (ofGameForm g) =m (imagePred A) (ofGameForm h) ↔ g =m A h := by
  constructor
  · intro h1 x hx
    have := h1 (ofGameForm x) ⟨x, hx, rfl⟩
    rwa [←ofGameForm_add, ←ofGameForm_add,
         misereOutcome_ofGameForm, misereOutcome_ofGameForm] at this
  · rintro h1 a ⟨x, hx, rfl⟩
    rw [←ofGameForm_add, ←ofGameForm_add,
        misereOutcome_ofGameForm, misereOutcome_ofGameForm]
    exact h1 x hx

theorem ofGameForm_ofSets (st : Player → Set GameForm.{u})
    [Small.{u} (st .left)] [Small.{u} (st .right)] :
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

theorem ofGameForm_dicotic (B' C' : Set GameForm.{u}) [Small.{u} B'] [Small.{u} C'] :
    ofGameForm !{B' | C'} = !{ofGameForm '' B' | ofGameForm '' C'} := by
  convert ofGameForm_ofSets ( fun p => p.casesOn B' C' )
  · rename_i p; cases p <;> rfl
  · cases ‹Player› <;> rfl

variable {U : GameForm.{u} → Prop}

instance imagePred_closedUnderSum [ClosedUnderAdd U] : ClosedUnderAdd (imagePred U) where
  has_add := by
    rintro g h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    use x + y
    simp [ofGameForm_add, *]
    convert (ClosedUnderAdd.has_add x y hx hy) using 1

instance imagePred_hereditary [Hereditary U] : Hereditary (imagePred U) where
  has_option := by
    rintro g g' ⟨x, hx, rfl⟩ ⟨p, ⟨⟨q, rfl⟩, hp⟩⟩
    obtain ⟨y, hy, rfl⟩ := mem_moves_ofGameForm hp
    exact ⟨y, Hereditary.of_mem_moves hx hy, rfl⟩

instance imagePred_closedUnderNeg [ClosedUnderNeg U] : ClosedUnderNeg (imagePred U) where
  neg_of := by
    rintro g ⟨x, hx, rfl⟩
    use -x
    simp [hx, ofGameForm_neg]

instance imagePred_closedUnderDicotic [ClosedUnderDicotic IsShort U] :
    ClosedUnderDicotic IsShort (imagePred U) where
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
    haveI hsB : Small.{u} B' :=
      small_of_injective (show Function.Injective (fun x : B' => (⟨ofGameForm x, by
          rw [hB']; exact Set.mem_image_of_mem _ x.2⟩ : B)) from
        fun x y hxy => by simpa [Subtype.ext_iff] using
          ofGameForm_Injective (by simpa [Subtype.ext_iff] using hxy))
    haveI hsC : Small.{u} C' :=
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

instance imagePred_shortUniverse [ShortUniverse U] : ShortUniverse (imagePred U) where
  zero_mem := by
    use 0; simp [ofGameForm_zero]
    exact ‹ShortUniverse U›.zero_mem
  isAmbient_of_mem := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact isShort_ofGameForm_iff.mpr (‹ShortUniverse U›.isAmbient_of_mem hx)

/--
This is part of [Siegel (Definition 5.20 on p. 220)][siegel:GeneralDeadendingUniverse:2025]
-/
def AtomicReversibleLeft (A : AugmentedForm.{u} → Prop) (g gl : AugmentedForm.{u}) : Prop :=
  ∃ glr ∈ moves .right gl, (g ≥m A glr) ∧ Form.IsEnd .left glr

/--
This is part of [Siegel (Definition 5.20 on p. 220)][siegel:GeneralDeadendingUniverse:2025]
-/
def AtomicReversibleRight (A : AugmentedForm.{u} → Prop) (g gr : AugmentedForm.{u}) : Prop :=
  ∃ grl ∈ moves .left gr, (grl ≥m A g) ∧ Form.IsEnd .right grl

theorem atomicReversibleLeft_neg {A : AugmentedForm.{u} → Prop} [ClosedUnderNeg A]
    {u uR : AugmentedForm.{u}} (h : AtomicReversibleRight A u uR) :
    AtomicReversibleLeft A (-u) (-uR) := by
  obtain ⟨uRL, hmem, hge, hend⟩ := h
  refine ⟨-uRL, ?_, ?_, ?_⟩
  · simp only [moves_neg, Set.mem_neg, neg_neg, Player.neg_right]; exact hmem
  · rw [ClosedUnderNeg.neg_ge_neg_iff]; exact hge
  · rw [IsEnd.neg_iff_neg]; simpa using hend

theorem atomicReversibleRight_neg {A : AugmentedForm.{u} → Prop} [ClosedUnderNeg A]
    {u uL : AugmentedForm.{u}} (h : AtomicReversibleLeft A u uL) :
    AtomicReversibleRight A (-u) (-uL) := by
  obtain ⟨uLR, hmem, hge, hend⟩ := h
  refine ⟨-uLR, ?_, ?_, ?_⟩
  · simp only [moves_neg, Set.mem_neg, neg_neg, Player.neg_left]; exact hmem
  · rw [ClosedUnderNeg.neg_ge_neg_iff]; exact hge
  · rw [IsEnd.neg_iff_neg]; simpa using hend

/--
This is [Siegel (Definition 5.20 on p. 220)][siegel:GeneralDeadendingUniverse:2025]
-/
def IsExpansion (A : AugmentedForm.{u} → Prop) (u g : AugmentedForm.{u}) : Prop :=
  (A u) ∧
  -- (i)
  (∀ gL ∈ moves .left g, ∃ uL ∈ moves .left u, IsExpansion A uL gL) ∧
  (¬ IsEndLike .left g → ∀ uL ∈ moves .left u,
      ∃ gL : moves .left g, IsExpansion A uL gL.1) ∧
  -- (ii)
  (IsEndLike .left g →
    (∀ uL ∈ moves .left u,
        (∃ gL : moves .left g, IsExpansion A uL gL.1) ∨ AtomicReversibleLeft A u uL) ∧
    (¬ Form.IsEnd .left u → ∃ uL ∈ moves .left u, AtomicReversibleLeft A u uL)) ∧
  -- (iii)
  (∀ gR ∈ moves .right g, ∃ uR ∈ moves .right u, IsExpansion A uR gR) ∧
  -- (iv)
  (¬ IsEndLike .right g → ∀ uR ∈ moves .right u,
      ∃ gR : moves .right g, IsExpansion A uR gR.1) ∧
  -- (v)
  (IsEndLike .right g →
    (∀ uR ∈ moves .right u,
        (∃ gR : moves .right g, IsExpansion A uR gR.1) ∨ AtomicReversibleRight A u uR) ∧
    (¬ Form.IsEnd .right u → ∃ uR ∈ moves .right u, AtomicReversibleRight A u uR))
termination_by g
decreasing_by form_wf


theorem isExpansion_iff (A : AugmentedForm.{u} → Prop) (u g : AugmentedForm.{u}) :
    IsExpansion A u g ↔
  (A u) ∧
  (∀ gL ∈ moves .left g, ∃ uL ∈ moves .left u, IsExpansion A uL gL) ∧
  (¬ IsEndLike .left g → ∀ uL ∈ moves .left u,
      ∃ gL : moves .left g, IsExpansion A uL gL.1) ∧
  (IsEndLike .left g →
    (∀ uL ∈ moves .left u,
        (∃ gL : moves .left g, IsExpansion A uL gL.1) ∨ AtomicReversibleLeft A u uL) ∧
    (¬ Form.IsEnd .left u → ∃ uL ∈ moves .left u, AtomicReversibleLeft A u uL)) ∧
  (∀ gR ∈ moves .right g, ∃ uR ∈ moves .right u, IsExpansion A uR gR) ∧
  (¬ IsEndLike .right g → ∀ uR ∈ moves .right u,
      ∃ gR : moves .right g, IsExpansion A uR gR.1) ∧
  (IsEndLike .right g →
    (∀ uR ∈ moves .right u,
        (∃ gR : moves .right g, IsExpansion A uR gR.1) ∨ AtomicReversibleRight A u uR) ∧
    (¬ Form.IsEnd .right u → ∃ uR ∈ moves .right u, AtomicReversibleRight A u uR)) := by
  rw [IsExpansion]

theorem isExpansion_self_of_tombstoneFree (A : AugmentedForm.{u} → Prop) [Hereditary A]
    {g : AugmentedForm.{u}} (hg : A g) (h_tombstoneFree : TombstoneFree g) :
    IsExpansion A g g := by
  revert h_tombstoneFree
  induction g using AugmentedForm.moveRecOn with
  | mk g ih =>
    intro h_tombstoneFree
    have hendL : IsEndLike .left g → Form.IsEnd .left g := fun h =>
      (IsEndLike_iff.mp h).resolve_left (h_tombstoneFree.not_hasTombstone .left)
    have hendR : IsEndLike .right g → Form.IsEnd .right g := fun h =>
      (IsEndLike_iff.mp h).resolve_left (h_tombstoneFree.not_hasTombstone .right)
    rw [isExpansion_iff]
    refine ⟨hg, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro gL hgL
      exact ⟨gL, hgL, ih .left gL hgL (Hereditary.of_mem_moves hg hgL) (h_tombstoneFree.moves .left gL hgL)⟩
    · intro _ uL huL
      exact ⟨⟨uL, huL⟩, ih .left uL huL (Hereditary.of_mem_moves hg huL) (h_tombstoneFree.moves .left uL huL)⟩
    · intro hend
      have he := hendL hend; rw [isEnd_def] at he
      exact ⟨fun uL huL => absurd (he ▸ huL) (by simp), fun hne => absurd (hendL hend) hne⟩
    · intro gR hgR
      exact ⟨gR, hgR, ih .right gR hgR (Hereditary.of_mem_moves hg hgR) (h_tombstoneFree.moves .right gR hgR)⟩
    · intro _ uR huR
      exact ⟨⟨uR, huR⟩, ih .right uR huR (Hereditary.of_mem_moves hg huR) (h_tombstoneFree.moves .right uR huR)⟩
    · intro hend
      have he := hendR hend; rw [isEnd_def] at he
      exact ⟨fun uR huR => absurd (he ▸ huR) (by simp), fun hne => absurd (hendR hend) hne⟩
/--
By $\hat{\mathcal{U}}$ we denote the set of all $G \in \hat{\mathcal{M}}
such that $G$ has a $\mathcal{U}$-expansion.

This is [Siegel (Definition 5.20 on p. 220)][siegel:GeneralDeadendingUniverse:2025]
-/
def ExpansionSet (A : GameForm.{u} → Prop) (g : AugmentedForm.{u}) : Prop :=
  IsShort g ∧ ∃ u, IsExpansion (imagePred A) u g

/--
This is [Siegel (Lemma 5.21 on p. 220)][siegel:GeneralDeadendingUniverse:2025]

Proof idea:
We can assume that $u$ has no $U$-dominated options, since eliminating $U$-dominated options does
not change the simplest form of $u$.
Likewise, we can assume that $u$ has no ordinary $U$-reversible options.
Now let $v$ be obtained from $u$ by removing any atomic $U$-reversible options that can be removed
without (i) changing the value of $u$, or (ii) turning $u$ into an end.
We claim that $v$ is a $U$-expansion of $G$.
Now $G$ is obtained from $v$ by tombstone replacement and tombstone erasure
(applied to various subpositions of $v$).
Thus every ordinary $G^L$ is obtained from some $v^L$ in this way.
By induction, $V^L$ is a $U$-expansion of $G^L$ , which proves conditions (i) and (ii) in
Definition 5.20. For (iii), suppose that G is Left end-like.
If $G$ has no ordinary Left options, then every $u^L$ must be atomic $U$-reversible;
otherwise, $G$ has Left tombstone , and so must be obtained by tombstone replacement of at
least one atomic $U$-reversible $u^L$.
-/
theorem ExpansionSet_simplestForm_mem {U : GameForm.{u} → Prop} [ShortUniverse U]
    {u g : AugmentedForm.{u}} (hg : ExpansionSet U u) (hkShort : IsShort g)
    (hkSimp : SimplestForm (ExpansionSet U) g) (hkEq : g =m (ExpansionSet U) u) :
    ExpansionSet U g := by
  sorry

/--
This is [Siegel (Theorem 5.22 on p. 220)][siegel:GeneralDeadendingUniverse:2025]

Proof idea:
There are four cases. In each case, we show that it is possible to apply a series of reductions to the Left options of U + V , resulting in an expression that meets the Left conditions of Definition 5.20. The analogous Right conditions then follow by symmetry.

Case 1: Neither G nor H is Left end-like. Then for every ordinary G L , we know that some U L is a U-expansion of G L , so by induction, U L + V is equal to a U-expansion of G L + H . Similarly, for every ordinary H L , some U +V L is equal to a U-expansion of G + H L . By the definition of U-expansion, this must cover all the Left options of U and V , and the conclusion follows by replacement.

Case 2: G is Left end-like and H is not. Consider any atomic U-reversible Left option U L1, reversible through U L1 R1 ≤U U . Then U L1 + V is reversible through U L1 R1 + V , and since V is not a Left end, we can bypass it. Therefore  U + V ≡U {U L1 R1 + V L, U L′  + V , U + V L | (U + V )R},  where U L′ is understood to range over all Left options of U except U L1. But since U L1 R1 ≤U U , all the options of the form U L1 R1 + V L are dominated and can be excluded. We can repeat the procedure with any atomic U-reversible Left option of U, so that in fact  U + V ≡U {U L′  + V , U + V L | (U + V )R},  where U L′ ranges over all Left options of U that are not atomic U-reversible. Since G + H is not Left end-like, the rest of the argument proceeds just as in Case 1.

Case 3: H is Left end-like and G is not. This case is identical to Case 2, by symmetry.

Case 4a: G and H are both Left end-like, and neither U nor V is a Left end. Consider a U L1 that is atomic U-reversible through U L1 R1. It can be bypassed, so that  U + V ≡U {U L1 R1 + V L, U L′  + V , U + V L | (U + V )R},  exactly as in Case 2. Also as in Case 2, options of the form U L1 R1 + V L are dominated and can be excluded, eventually obtaining  U + V ≡U {U L′  + V , U + V L | (U + V )R}.  We can repeat with any V L1 that is atomic U-reversible:  U + V ≡U {U L + V L1 R1 , U L′  + V, U + V L′  | (U + V )R}.  Options of the form U L + V L1 R1 are dominated and can be excluded — except in the specific case where U L is atomic U-reversible (in which case U L + V has already been eliminated). But in that case, since V L1 R1 is a Left end, it follows that U L + V L1 R1 is also atomic U-reversible. We are left with  U + V ≡U {T , U L′  + V, U + V L′  | (U + V )R},  where U L′ ranges over Left options of U that are not atomic U-reversible; V L′ ranges over Left options of V that are not atomic U-reversible; and T ranges over various (and at least one) atomic U-reversible options of U + V . Since G + H is Left end-like, this completes the proof.
-/
theorem expansion_add_mem {U : GameForm.{u} → Prop} [ShortUniverse U]
    {u g u' g' : AugmentedForm.{u}} (hu : imagePred U u) (hu' : imagePred U u')
    (hg : IsShort g) (hg' : IsShort g')
    (h : IsExpansion (imagePred U) u g) (h' : IsExpansion (imagePred U) u' g') :
    ∃ w, IsExpansion (imagePred U) w (g + g') := by
  sorry
