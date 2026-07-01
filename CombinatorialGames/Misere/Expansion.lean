/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.SimplestForm
public import CombinatorialGames.AugmentedForm.AugmentedSet

public section

open AugmentedForm
open Form
open Form.Misere.Outcome

universe u

/--
This is part of [Siegel (Definition 5.20 on p. 220)][siegel:GeneralDeadendingUniverse:2025]
-/
def AtomicReversibleLeft (A : AugmentedForm → Prop) (g gl : AugmentedForm) : Prop :=
  ∃ glr ∈ moves .right gl, (g ≥m A glr) ∧ Form.IsEnd .left glr

/--
This is part of [Siegel (Definition 5.20 on p. 220)][siegel:GeneralDeadendingUniverse:2025]
-/
def AtomicReversibleRight (A : AugmentedForm → Prop) (g gr : AugmentedForm) : Prop :=
  ∃ grl ∈ moves .left gr, (grl ≥m A g) ∧ Form.IsEnd .right grl

def AtomicReversible (A : AugmentedForm → Prop) (p : Player) (g g' : AugmentedForm) : Prop :=
  Player.cases (AtomicReversibleLeft A g g') (AtomicReversibleRight A g g') p

theorem atomicReversibleLeft_neg {A : AugmentedForm → Prop} [ClosedUnderNeg A]
    {u uR : AugmentedForm} (h : AtomicReversibleRight A u uR) :
    AtomicReversibleLeft A (-u) (-uR) := by
  obtain ⟨uRL, hmem, hge, hend⟩ := h
  refine ⟨-uRL, ?_, ?_, ?_⟩
  · simp only [moves_neg, Set.mem_neg, neg_neg, Player.neg_right]; exact hmem
  · rw [ClosedUnderNeg.neg_ge_neg_iff]; exact hge
  · rw [IsEnd.neg_iff_neg]; simpa using hend

theorem atomicReversibleRight_neg {A : AugmentedForm → Prop} [ClosedUnderNeg A]
    {u uL : AugmentedForm} (h : AtomicReversibleLeft A u uL) :
    AtomicReversibleRight A (-u) (-uL) := by
  obtain ⟨uLR, hmem, hge, hend⟩ := h
  refine ⟨-uLR, ?_, ?_, ?_⟩
  · simp only [moves_neg, Set.mem_neg, neg_neg, Player.neg_left]; exact hmem
  · rw [ClosedUnderNeg.neg_ge_neg_iff]; exact hge
  · rw [IsEnd.neg_iff_neg]; simpa using hend

theorem atomicReversible_neg {A : AugmentedForm → Prop} [ClosedUnderNeg A] {p : Player}
    {u u' : AugmentedForm} (h : AtomicReversible A p u u') :
    AtomicReversible A (-p) (-u) (-u') := by
  cases p with
  | left => exact atomicReversibleRight_neg h
  | right => exact atomicReversibleLeft_neg h

@[expose]
def IsPlayerExpansion (A : GameForm → Prop) (p : Player) (u g : AugmentedForm) : Prop :=
  ((AugmentedSet A) u) ∧
  -- (i)
  (∀ g' ∈ moves p g, ∃ u' ∈ moves p u,
      IsPlayerExpansion A .left u' g' ∧ IsPlayerExpansion A .right u' g') ∧
  -- (ii)
  (¬ IsEndLike p g → ∀ u' ∈ moves p u, ∃ g' : moves p g,
      IsPlayerExpansion A .left u' g'.val ∧ IsPlayerExpansion A .right u' g'.val) ∧
  -- (iii)
  (IsEndLike p g →
    (∀ u' ∈ moves p u,
        (∃ g' : moves p g,
            IsPlayerExpansion A .left u' g'.val ∧ IsPlayerExpansion A .right u' g'.val)
          ∨ AtomicReversible (AugmentedSet A) p u u') ∧
    (¬ IsEnd p u → ∃ u' ∈ moves p u, AtomicReversible (AugmentedSet A) p u u'))
termination_by g
decreasing_by form_wf

/--
`IsExpansion U u g` means that `u` is a `U`-expansion of `g`.

This is [Siegel (Definition 5.20 on p. 220)][siegel:GeneralDeadendingUniverse:2025]
-/
@[expose] def IsExpansion (A : GameForm → Prop) (u g : AugmentedForm) : Prop :=
  IsPlayerExpansion A .left u g ∧ IsPlayerExpansion A .right u g

theorem isExpansion_of_isPlayerExpansion {A : GameForm → Prop}
  {u g : AugmentedForm}
  (h1 : ∀ p, IsPlayerExpansion A p u g) : IsExpansion A u g := ⟨h1 .left, h1 .right⟩

theorem isPlayerExpansion_of_isExpansion {A : GameForm → Prop} {u g : AugmentedForm}
    (h1 : IsExpansion A u g) (p : Player) : IsPlayerExpansion A p u g := by
  unfold IsExpansion at h1
  cases p
  · exact h1.left
  · exact h1.right

/--
Condition (i)
-/
theorem IsExpansion.expander_of_mem_moves {A : GameForm → Prop}
    {u g gp : AugmentedForm} {p : Player} (h : IsExpansion A u g) (hgp : gp ∈ moves p g) :
    ∃ up ∈ moves p u, IsExpansion A up gp := by
  have hp := isPlayerExpansion_of_isExpansion h p
  unfold IsPlayerExpansion at hp
  obtain ⟨up, hup, hL, hR⟩ := hp.2.1 gp hgp
  exact ⟨up, hup, hL, hR⟩

/--
Condition (ii)
-/
theorem IsExpansion.base_of_mem_moves_of_not_endLike {A : GameForm → Prop}
    {u g up : AugmentedForm} {p : Player} (h : IsExpansion A u g) (hne : ¬ IsEndLike p g)
    (hup : up ∈ moves p u) : ∃ gp ∈ moves p g, IsExpansion A up gp := by
  have hp := isPlayerExpansion_of_isExpansion h p
  unfold IsPlayerExpansion at hp
  obtain ⟨gp, hL, hR⟩ := hp.2.2.1 hne up hup
  exact ⟨gp.val, gp.property, hL, hR⟩

/--
Condition (iii)
-/
theorem IsExpansion.base_or_atomicReversible_of_endLike {A : GameForm → Prop}
    {u g up : AugmentedForm} {p : Player} (h : IsExpansion A u g) (hel : IsEndLike p g)
    (hup : up ∈ moves p u) :
    (∃ gp ∈ moves p g, IsExpansion A up gp) ∨ AtomicReversible (AugmentedSet A) p u up := by
  have hp := isPlayerExpansion_of_isExpansion h p
  unfold IsPlayerExpansion at hp
  rcases (hp.2.2.2 hel).1 up hup with ⟨gp, hL, hR⟩ | hrev
  · exact Or.inl ⟨gp.val, gp.property, hL, hR⟩
  · exact Or.inr hrev

theorem isPlayerExpansion_self_of_tombstoneFree (A : GameForm → Prop) [Hereditary A]
    (p : Player) {g : AugmentedForm} (hg : (AugmentedSet A) g) (h_tombstoneFree : TombstoneFree g) :
    IsPlayerExpansion A p g g := by
  -- Strong induction on `g` (via `AugmentedForm.moveRecOn`).
  induction g using AugmentedForm.moveRecOn generalizing p with
  | _ x ih =>
    -- Each ordinary option `g'` of `x` is again `A`-valid and tombstone-free, so by the
    -- induction hypothesis it is its own expansion for either player.
    have h_opt : ∀ g' ∈ moves p x, ∀ q : Player, IsPlayerExpansion A q g' g' := by
      intro g' hg' q
      exact ih p g' hg' q (Hereditary.of_mem_moves hg hg') (h_tombstoneFree.moves p g' hg')
    unfold IsPlayerExpansion
    refine ⟨hg, ?_, ?_, ?_⟩
    · -- (i) each option is expanded by itself
      intro g' hg'
      exact ⟨g', hg', h_opt g' hg' .left, h_opt g' hg' .right⟩
    · -- (ii) non-end-like case: again pick the option itself
      intro _ u' hu'
      exact ⟨⟨u', hu'⟩, h_opt u' hu' .left, h_opt u' hu' .right⟩
    · -- (iii) end-like case
      intro h_end
      refine ⟨?_, ?_⟩
      · intro u' hu'
        exact Or.inl ⟨⟨u', hu'⟩, h_opt u' hu' .left, h_opt u' hu' .right⟩
      · -- `x` is tombstone-free, so `IsEndLike p x` forces `IsEnd p x`, contradicting `¬IsEnd p x`.
        intro h_not_end
        exfalso
        rcases IsEndLike_iff.mp h_end with h_tomb | h_is_end
        · exact h_tombstoneFree.not_hasTombstone p h_tomb
        · exact h_not_end h_is_end

theorem isExpansion_self_of_tombstoneFree (A : GameForm → Prop) [Hereditary A]
    {g : AugmentedForm} (hg : (AugmentedSet A) g) (h_tombstoneFree : TombstoneFree g) :
    IsExpansion A g g := 
  isExpansion_of_isPlayerExpansion
    (fun p => isPlayerExpansion_self_of_tombstoneFree A p hg h_tombstoneFree)

variable {U : GameForm → Prop}

theorem isExpansion_strong_left [ShortUniverse U] {u g : AugmentedForm}
    (hu : IsShort u) (h : IsExpansion U u g)
    (hp : IsEndLike .left g) : Strong (AugmentedSet U) u .left := by
  by_cases hend : Form.IsEnd .left u
  · exact strong_of_isEndLike (Or.inr hend)
  · unfold IsExpansion IsPlayerExpansion at h
    obtain ⟨uL, huL, ulr, hulr_mem, hge, hulr_end⟩ := (h.1.2.2.2 hp).2 hend
    have hrev : ReversibleLeftThrough (AugmentedSet U) u uL ulr := ⟨huL, hulr_mem, hge⟩
    have heq : (atomicReplaceLeft u uL) =m (AugmentedSet U) u :=
      atomicReplaceLeft_misereEQ hu hrev hulr_end
    have hstrong : Strong (AugmentedSet U) (atomicReplaceLeft u uL) .left :=
      strong_of_isEndLike (Or.inl (hasTombstone_left_atomicReplaceLeft u uL))
    exact (strong_congr_misereEQ heq).mp hstrong

theorem isPlayerExpansion_neg {A : GameForm → Prop} [ClosedUnderNeg A] {p : Player}
    {u g : AugmentedForm} (h : IsPlayerExpansion A p u g) :
    IsPlayerExpansion A (-p) (-u) (-g) := by
  induction g using AugmentedForm.moveRecOn generalizing p u with
  | _ x ih =>
    unfold IsPlayerExpansion at h ⊢
    -- `moves` of a negation: `moves (-p) (-y) = -(moves p y)`.
    have h_moves_x : moves (-p) (-x) = -(moves p x) := by rw [moves_neg, neg_neg]
    have h_moves_u : moves (-p) (-u) = -(moves p u) := by rw [moves_neg, neg_neg]
    refine ⟨ClosedUnderNeg.neg_of h.1, ?_, ?_, ?_⟩
    · -- (i) ordinary options
      intro g' hg'
      rw [h_moves_x, Set.mem_neg] at hg'
      obtain ⟨u', hu', h_left, h_right⟩ := h.2.1 (-g') hg'
      refine ⟨-u', ?_, ?_, ?_⟩
      · rw [h_moves_u, Set.mem_neg, neg_neg]; exact hu'
      · simpa using ih p (-g') hg' h_right
      · simpa using ih p (-g') hg' h_left
    · -- (ii) non-end-like case
      intro h_not_end u' hu'
      rw [IsEndLike.neg_iff_neg, neg_neg] at h_not_end
      rw [h_moves_u, Set.mem_neg] at hu'
      obtain ⟨g'', h_left, h_right⟩ := h.2.2.1 h_not_end (-u') hu'
      refine ⟨⟨-g''.val, ?_⟩, ?_, ?_⟩
      · rw [h_moves_x, Set.mem_neg, neg_neg]; exact g''.property
      · simpa using ih p g''.val g''.property h_right
      · simpa using ih p g''.val g''.property h_left
    · -- (iii) end-like case
      intro h_end
      rw [IsEndLike.neg_iff_neg, neg_neg] at h_end
      obtain ⟨h_partA, h_partB⟩ := h.2.2.2 h_end
      refine ⟨?_, ?_⟩
      · intro u' hu'
        rw [h_moves_u, Set.mem_neg] at hu'
        rcases h_partA (-u') hu' with ⟨g'', h_left, h_right⟩ | h_rev
        · refine Or.inl ⟨⟨-g''.val, ?_⟩, ?_, ?_⟩
          · rw [h_moves_x, Set.mem_neg, neg_neg]; exact g''.property
          · simpa using ih p g''.val g''.property h_right
          · simpa using ih p g''.val g''.property h_left
        · exact Or.inr (by simpa using atomicReversible_neg h_rev)
      · intro h_not_end
        rw [IsEnd.neg_iff_neg, neg_neg] at h_not_end
        obtain ⟨u', hu', h_rev⟩ := h_partB h_not_end
        refine ⟨-u', ?_, ?_⟩
        · rw [h_moves_u, Set.mem_neg, neg_neg]; exact hu'
        · exact atomicReversible_neg h_rev

theorem isExpansion_neg (A : GameForm → Prop) [ClosedUnderNeg A]
    {u g : AugmentedForm} (h : IsExpansion A u g) : IsExpansion A (-u) (-g) := by
  refine isExpansion_of_isPlayerExpansion (fun p => ?_)
  have hp := isPlayerExpansion_neg (isPlayerExpansion_of_isExpansion h (-p))
  rwa [neg_neg] at hp

theorem isExpansion_strong [ShortUniverse U] {u g : AugmentedForm} {p : Player}
    (hu : IsShort u) (h : IsExpansion U u g)
    (hp : IsEndLike p g) : Strong (AugmentedSet U) u p := by
  cases p with
  | left => exact isExpansion_strong_left hu h hp
  | right =>
    refine (Strong.neg_iff (g := u) (p := .left)).mp ?_
    refine isExpansion_strong_left (Short.neg hu) (isExpansion_neg U h) ?_
    simpa [IsEndLike.neg_iff_neg] using hp

/--
By $\hat{\mathcal{U}}$ we denote the set of all $G \in \hat{\mathcal{M}}
such that $G$ has a $\mathcal{U}$-expansion.

`ExpansionSet U g` means that `g` has `U`-expansion

This is [Siegel (Definition 5.20 on p. 220)][siegel:GeneralDeadendingUniverse:2025]
-/
@[expose] def ExpansionSet (U : GameForm.{u} → Prop) (g : AugmentedForm.{u}) : Prop :=
  IsShort g ∧ ∃ u, IsExpansion U u g

theorem expansionSet_mem_ofGameForm [ShortUniverse U] (g : GameForm) (ha : U g) :
    ExpansionSet U (ofGameForm g) := by
  refine ⟨?_, ?_⟩
  · exact isShort_ofGameForm_iff.mpr (‹ShortUniverse U›.isAmbient_of_mem ha)
  · exact ⟨ofGameForm g, isExpansion_self_of_tombstoneFree U
      ⟨g, ha, rfl⟩ (ofGameForm_tombstoneFree g)⟩

theorem augmentedSet_subset_expansionSet [ShortUniverse U] {x : AugmentedForm}
    (hx : (AugmentedSet U) x) : ExpansionSet U x := by
  obtain ⟨w, hw, rfl⟩ := hx
  exact expansionSet_mem_ofGameForm w hw

theorem isShort_of_isExpansion [ShortUniverse U] {g u : AugmentedForm}
    (hexp : IsExpansion U u g) : IsShort u := by
  have h1 := hexp.1
  unfold IsPlayerExpansion at h1
  obtain ⟨x, hx, rfl⟩ := h1.1
  exact isShort_ofGameForm_iff.mpr (‹ShortUniverse U›.isAmbient_of_mem hx)

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
theorem expansionSet_simplestForm_mem [ShortUniverse U]
    {u g : AugmentedForm} (hg : ExpansionSet U u) (hkShort : IsShort g)
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
theorem expansion_add_mem {U : GameForm → Prop} [ShortUniverse U]
    {g h u v : AugmentedForm}
    (hg : IsShort g) (hg' : IsShort h)
    (h_u_exp : IsExpansion U u g) (h_v_exp : IsExpansion U v h) :
    ∃ w, IsExpansion U w (g + h) ∧ w =m (AugmentedSet U) (u + v) := by
  sorry

instance [ShortUniverse U] : ClosedUnderAdd (ExpansionSet U) where
  has_add := by
    intro g g' hg hg'
    unfold ExpansionSet at ⊢ hg hg'
    obtain ⟨hgS, u, hexp⟩ := hg
    obtain ⟨hg'S, u', hexp'⟩ := hg'
    obtain ⟨w, hwexp, _⟩ := expansion_add_mem hgS hg'S hexp hexp'
    exact ⟨Short.add hgS hg'S, w, hwexp⟩

theorem isExpansion_isEnd_left {u g : AugmentedForm}
    (h : IsExpansion U u g) (hu : Form.IsEnd .left u) : Form.IsEnd .left g := by
  have h_left := h.1
  unfold IsPlayerExpansion at h_left
  rw [isEnd_def] at *
  rw [Set.eq_empty_iff_forall_notMem]
  intro g' hg'
  obtain ⟨u', hu', _⟩ := h_left.2.1 g' hg'
  rw [hu] at hu'
  exact Set.notMem_empty u' hu'

theorem isExpansion_isEnd_right [ShortUniverse U] {u g : AugmentedForm}
    (h : IsExpansion U u g) (hu : Form.IsEnd .right u) : Form.IsEnd .right g := by
  have hneg := isExpansion_isEnd_left (isExpansion_neg U h)
    (IsEnd.neg_iff_neg.mpr hu)
  exact IsEnd.neg_iff_neg.mp hneg

private def ExpansionProps (U : GameForm → Prop) (g u : AugmentedForm) : Prop :=
    (∀ h, IsShort h → Form.IsEnd .left h → u ≥m (AugmentedSet U) h → IsEndLike .left g →
        g ≥m (AugmentedSet U) h) ∧
    (∀ h, IsShort h → Form.IsEnd .right h → h ≥m (AugmentedSet U) u → IsEndLike .right g →
        h ≥m (AugmentedSet U) g) ∧
    g =m (AugmentedSet U) u

theorem exists_rightMove_ge_of_isEnd_left [ShortUniverse U] {y z h : AugmentedForm}
    (hy : IsShort y) (hh : IsShort h) (hge : y ≥m (AugmentedSet U) h)
    (hz : z ∈ moves .right y) (hz_end : Form.IsEnd .left z) :
    ∃ hr ∈ moves .right h, z ≥m (AugmentedSet U) hr := by
  rcases (Form.ComparisonSet.maintenance_proviso_of_misereGE hy hh hge).1 z hz with
    h_opt | ⟨zl, hzl, _⟩
  · exact h_opt
  · rw [Form.isEnd_def] at hz_end
    rw [hz_end] at hzl
    exact absurd hzl (Set.notMem_empty _)

theorem exists_leftMove_le_of_isEnd_right [ShortUniverse U] {y z h : AugmentedForm}
    (hy : IsShort y) (hh : IsShort h) (hge : h ≥m (AugmentedSet U) y)
    (hz : z ∈ moves .left y) (hz_end : Form.IsEnd .right z) :
    ∃ hl ∈ moves .left h, hl ≥m (AugmentedSet U) z := by
  rcases (Form.ComparisonSet.maintenance_proviso_of_misereGE hh hy hge).2.1 z hz with
    h_opt | ⟨zr, hzr, _⟩
  · exact h_opt
  · rw [Form.isEnd_def] at hz_end
    rw [hz_end] at hzr
    exact absurd hzr (Set.notMem_empty _)

private theorem expansionProps_Rleft [ShortUniverse U] {g u : AugmentedForm}
    (IH : ∀ (g0 u0 : AugmentedForm), treeSize g0 < treeSize g → IsShort g0 →
        IsExpansion U u0 g0 → ExpansionProps U g0 u0)
    (hg : IsShort g) (hexp : IsExpansion U u g) :
    ∀ h, IsShort h → Form.IsEnd .left h → u ≥m (AugmentedSet U) h → IsEndLike .left g →
        g ≥m (AugmentedSet U) h := by
  intro h hh hh_left hu_ge hg_left
  have hu := isShort_of_isExpansion hexp
  have h_maint : Maintenance (AugmentedSet U) g h .right := by
    have h_maint_u : Maintenance (AugmentedSet U) u h .right :=
      (Form.ComparisonSet.maintenance_proviso_of_misereGE hu hh hu_ge).1
    intro gr hgr
    obtain ⟨ur, hur, hexp_gr⟩ := hexp.expander_of_mem_moves hgr
    have hgr_short := Short.of_mem_moves hg hgr
    have hlt := treeSize_lt_of_mem_moves hg hgr
    have hur_short := Short.of_mem_moves hu hur
    obtain ⟨hRLgr, _, hEQgr⟩ := IH gr ur hlt hgr_short hexp_gr
    rcases h_maint_u ur hur with ⟨hr, hhr, hur_ge⟩ | ⟨url, hurl, hurl_ge⟩
    · exact Or.inl ⟨hr, hhr, (misereGE_of_misereEQ hEQgr).trans hur_ge⟩
    · by_cases hgr_el : IsEndLike .left gr
      · rcases hexp_gr.base_or_atomicReversible_of_endLike hgr_el hurl with
          ⟨grl, hgrl, hexp_grl⟩ | hrev
        · have hgrl_short := Short.of_mem_moves hgr_short hgrl
          have hlt2 := (treeSize_lt_of_mem_moves hgr_short hgrl).trans hlt
          have hEQ := (IH grl url hlt2 hgrl_short hexp_grl).2.2
          exact Or.inr ⟨grl, hgrl, (misereGE_of_misereEQ hEQ).trans hurl_ge⟩
        · obtain ⟨urlr, hurlr, hur_ge_urlr, hurlr_end⟩ := hrev
          obtain ⟨hr, hhr, hr_ge⟩ :=
            exists_rightMove_ge_of_isEnd_left (Short.of_mem_moves hur_short hurl)
              hh hurl_ge hurlr hurlr_end
          have hgr_ge : gr ≥m (AugmentedSet U) urlr :=
            hRLgr urlr (Short.of_mem_moves (Short.of_mem_moves hur_short hurl) hurlr)
              hurlr_end hur_ge_urlr hgr_el
          exact Or.inl ⟨hr, hhr, hgr_ge.trans hr_ge⟩
      · obtain ⟨grl, hgrl, hexp_grl⟩ := hexp_gr.base_of_mem_moves_of_not_endLike hgr_el hurl
        have hgrl_short := Short.of_mem_moves hgr_short hgrl
        have hlt2 := (treeSize_lt_of_mem_moves hgr_short hgrl).trans hlt
        have hEQ := (IH grl url hlt2 hgrl_short hexp_grl).2.2
        exact Or.inr ⟨grl, hgrl, (misereGE_of_misereEQ hEQ).trans hurl_ge⟩
  refine Hereditary.misereGE_of_maintenance_proviso (AugmentedSet U) h_maint ?_ ?_ ?_
  · intro hl hhl
    rw [Form.isEnd_def] at hh_left
    rw [hh_left] at hhl
    exact absurd hhl (Set.notMem_empty _)
  · exact fun hend => strong_mono_right hu_ge (isExpansion_strong hu hexp hend)
  · exact fun _ => strong_of_isEndLike hg_left

private theorem expansionProps_Rright [ShortUniverse U] {g u : AugmentedForm}
    (IH : ∀ (g0 u0 : AugmentedForm), treeSize g0 < treeSize g → IsShort g0 →
        IsExpansion U u0 g0 → ExpansionProps U g0 u0)
    (hg : IsShort g) (hexp : IsExpansion U u g) :
    ∀ h, IsShort h → Form.IsEnd .right h → h ≥m (AugmentedSet U) u → IsEndLike .right g →
        h ≥m (AugmentedSet U) g := by
  intro h hh hh_right hu_ge hg_right
  have hu := isShort_of_isExpansion hexp
  have h_maint : Maintenance (AugmentedSet U) h g .left := by
    have h_maint_u : Maintenance (AugmentedSet U) h u .left :=
      (Form.ComparisonSet.maintenance_proviso_of_misereGE hh hu hu_ge).2.1
    intro gl hgl
    obtain ⟨ul, hul, hexp_gl⟩ := hexp.expander_of_mem_moves hgl
    have hgl_short := Short.of_mem_moves hg hgl
    have hlt := treeSize_lt_of_mem_moves hg hgl
    have hul_short := Short.of_mem_moves hu hul
    obtain ⟨_, hRRgl, hEQgl⟩ := IH gl ul hlt hgl_short hexp_gl
    rcases h_maint_u ul hul with ⟨hl, hhl, hl_ge⟩ | ⟨ulr, hulr, hulr_ge⟩
    · exact Or.inl ⟨hl, hhl, hl_ge.trans (misereGE_of_misereEQ hEQgl.symm)⟩
    · by_cases hgl_el : IsEndLike .right gl
      · rcases hexp_gl.base_or_atomicReversible_of_endLike hgl_el hulr with
          ⟨glr, hglr, hexp_glr⟩ | hrev
        · have hglr_short := Short.of_mem_moves hgl_short hglr
          have hlt2 := (treeSize_lt_of_mem_moves hgl_short hglr).trans hlt
          have hEQ := (IH glr ulr hlt2 hglr_short hexp_glr).2.2
          exact Or.inr ⟨glr, hglr, hulr_ge.trans (misereGE_of_misereEQ hEQ.symm)⟩
        · obtain ⟨ulrl, hulrl, hulrl_ge, hulrl_end⟩ := hrev
          obtain ⟨hl, hhl, hl_ge⟩ :=
            exists_leftMove_le_of_isEnd_right (Short.of_mem_moves hul_short hulr)
              hh hulr_ge hulrl hulrl_end
          have hgl_ge : ulrl ≥m (AugmentedSet U) gl :=
            hRRgl ulrl (Short.of_mem_moves (Short.of_mem_moves hul_short hulr) hulrl)
              hulrl_end hulrl_ge hgl_el
          exact Or.inl ⟨hl, hhl, hl_ge.trans hgl_ge⟩
      · obtain ⟨glr, hglr, hexp_glr⟩ := hexp_gl.base_of_mem_moves_of_not_endLike hgl_el hulr
        have hglr_short := Short.of_mem_moves hgl_short hglr
        have hlt2 := (treeSize_lt_of_mem_moves hgl_short hglr).trans hlt
        have hEQ := (IH glr ulr hlt2 hglr_short hexp_glr).2.2
        exact Or.inr ⟨glr, hglr, hulr_ge.trans (misereGE_of_misereEQ hEQ.symm)⟩
  refine Hereditary.misereGE_of_maintenance_proviso (AugmentedSet U) ?_ h_maint ?_ ?_
  · intro hr hhr
    rw [Form.isEnd_def] at hh_right
    rw [hh_right] at hhr
    exact absurd hhr (Set.notMem_empty _)
  · exact fun _ => strong_of_isEndLike hg_right
  · exact fun hend => strong_mono_left hu_ge (isExpansion_strong hu hexp hend)

private theorem expansionProps_EQ [ShortUniverse U] {g u : AugmentedForm}
    (IH : ∀ (g0 u0 : AugmentedForm), treeSize g0 < treeSize g → IsShort g0 →
        IsExpansion U u0 g0 → ExpansionProps U g0 u0)
    (hRL : ∀ h, IsShort h → Form.IsEnd .left h → u ≥m (AugmentedSet U) h → IsEndLike .left g →
        g ≥m (AugmentedSet U) h)
    (hRR : ∀ h, IsShort h → Form.IsEnd .right h → h ≥m (AugmentedSet U) u → IsEndLike .right g →
        h ≥m (AugmentedSet U) g)
    (hg : IsShort g) (hexp : IsExpansion U u g) :
    g =m (AugmentedSet U) u := by
  have hu := isShort_of_isExpansion hexp
  -- `u` is tombstone-free, so `p`-end-likeness of `u` is just `p`-endedness.
  have hu_notTomb : ∀ p, ¬ u.hasTombstone p := by
    have h1 := hexp.1
    unfold IsPlayerExpansion at h1
    obtain ⟨x, _, rfl⟩ := h1.1
    exact fun p => not_hasTombstone_ofGameForm x p
  have hu_isEnd : ∀ p, IsEndLike p u → Form.IsEnd p u :=
    fun p hp => (IsEndLike_iff.mp hp).resolve_left (hu_notTomb p)
  refine MisereEq.of_antisymm ?_ ?_
  · refine Hereditary.misereGE_of_maintenance_proviso (AugmentedSet U) ?_ ?_ ?_ ?_
    · intro gr hgr
      obtain ⟨ur, hur, hexp_gr⟩ := hexp.expander_of_mem_moves hgr
      have hEQ := (IH gr ur (treeSize_lt_of_mem_moves hg hgr) (Short.of_mem_moves hg hgr) hexp_gr).2.2
      exact Or.inl ⟨ur, hur, misereGE_of_misereEQ hEQ⟩
    · intro ul hul
      by_cases hg_el : IsEndLike .left g
      · rcases hexp.base_or_atomicReversible_of_endLike hg_el hul with ⟨gl, hgl, hexp_gl⟩ | hrev
        · have hEQ :=
            (IH gl ul (treeSize_lt_of_mem_moves hg hgl) (Short.of_mem_moves hg hgl) hexp_gl).2.2
          exact Or.inl ⟨gl, hgl, misereGE_of_misereEQ hEQ⟩
        · obtain ⟨ulr, hulr, hu_ge_ulr, hulr_end⟩ := hrev
          exact Or.inr ⟨ulr, hulr,
            hRL ulr (Short.of_mem_moves (Short.of_mem_moves hu hul) hulr) hulr_end hu_ge_ulr hg_el⟩
      · obtain ⟨gl, hgl, hexp_gl⟩ := hexp.base_of_mem_moves_of_not_endLike hg_el hul
        have hEQ :=
          (IH gl ul (treeSize_lt_of_mem_moves hg hgl) (Short.of_mem_moves hg hgl) hexp_gl).2.2
        exact Or.inl ⟨gl, hgl, misereGE_of_misereEQ hEQ⟩
    · exact fun h_end => isExpansion_strong hu hexp h_end
    · exact fun h_end =>
        strong_of_isEndLike (Or.inr (isExpansion_isEnd_left hexp (hu_isEnd .left h_end)))
  · refine Hereditary.misereGE_of_maintenance_proviso (AugmentedSet U) ?_ ?_ ?_ ?_
    · intro ur hur
      by_cases hg_el : IsEndLike .right g
      · rcases hexp.base_or_atomicReversible_of_endLike hg_el hur with ⟨gr, hgr, hexp_gr⟩ | hrev
        · have hEQ :=
            (IH gr ur (treeSize_lt_of_mem_moves hg hgr) (Short.of_mem_moves hg hgr) hexp_gr).2.2
          exact Or.inl ⟨gr, hgr, misereGE_of_misereEQ hEQ.symm⟩
        · obtain ⟨url, hurl, hurl_ge, hurl_end⟩ := hrev
          exact Or.inr ⟨url, hurl,
            hRR url (Short.of_mem_moves (Short.of_mem_moves hu hur) hurl) hurl_end hurl_ge hg_el⟩
      · obtain ⟨gr, hgr, hexp_gr⟩ := hexp.base_of_mem_moves_of_not_endLike hg_el hur
        have hEQ :=
          (IH gr ur (treeSize_lt_of_mem_moves hg hgr) (Short.of_mem_moves hg hgr) hexp_gr).2.2
        exact Or.inl ⟨gr, hgr, misereGE_of_misereEQ hEQ.symm⟩
    · intro gl hgl
      obtain ⟨ul, hul, hexp_gl⟩ := hexp.expander_of_mem_moves hgl
      have hEQ := (IH gl ul (treeSize_lt_of_mem_moves hg hgl) (Short.of_mem_moves hg hgl) hexp_gl).2.2
      exact Or.inl ⟨ul, hul, misereGE_of_misereEQ hEQ.symm⟩
    · exact fun h_end =>
        strong_of_isEndLike (Or.inr (isExpansion_isEnd_right hexp (hu_isEnd .right h_end)))
    · exact fun h_end => isExpansion_strong hu hexp h_end

private theorem isExpansion_props_step [ShortUniverse U] {g u : AugmentedForm}
    (IH : ∀ (g0 u0 : AugmentedForm), treeSize g0 < treeSize g → IsShort g0 →
        IsExpansion U u0 g0 → ExpansionProps U g0 u0)
    (hg : IsShort g) (hexp : IsExpansion U u g) :
    ExpansionProps U g u :=
  ⟨expansionProps_Rleft IH hg hexp, expansionProps_Rright IH hg hexp,
    expansionProps_EQ IH (expansionProps_Rleft IH hg hexp)
      (expansionProps_Rright IH hg hexp) hg hexp⟩

private theorem isExpansion_props [ShortUniverse U] {g u : AugmentedForm}
    (hg : IsShort g) (hexp : IsExpansion U u g) :
    ExpansionProps U g u :=
  isExpansion_props_step
    (fun _g0 _u0 _hlt hg0 hexp0 => isExpansion_props hg0 hexp0) hg hexp
termination_by treeSize g
decreasing_by assumption

/--
If $U$ is a $\mathcal{U}$-expansion of $G$ then $G =_{\matcal{U}} U$.
-/
theorem isExpansion_misereEQ [ShortUniverse U] {u g : AugmentedForm}
    (hg : IsShort g) (h : IsExpansion U u g) :
    g =m (AugmentedSet U) u :=
  (isExpansion_props hg h).2.2

theorem expansionSet_misereEQ_iff [ShortUniverse U] {p q : GameForm} (hp : U p) (hq : U q) :
    ((ofGameForm p) =m (ExpansionSet U) (ofGameForm q)) ↔ p =m U q := by
  constructor
  · intro H
    rw [← misereEQ_ofGameForm_iff]
    intro x hx
    exact H x (augmentedSet_subset_expansionSet hx)
  · intro H
    rw [← misereEQ_ofGameForm_iff] at H
    intro x hx
    obtain ⟨hxs, w, hexp⟩ := hx
    obtain ⟨hw, hw'⟩ := hexp
    have h_w_pred : AugmentedSet U w := by
      have h_left := hw
      unfold IsPlayerExpansion at h_left
      exact h_left.1
    have h_misere_eq : MisereOutcome (ofGameForm p + w) = MisereOutcome (ofGameForm q + w) :=
      H w h_w_pred
    have h_x_eq : x =m (AugmentedSet U) w := isExpansion_misereEQ hxs ⟨hw, hw'⟩
    have h_misere_eq_x : MisereOutcome (x + ofGameForm p) = MisereOutcome (w + ofGameForm p) :=
      h_x_eq (ofGameForm p) ⟨p, hp, rfl⟩
    have h_misere_eq_x' : MisereOutcome (x + ofGameForm q) = MisereOutcome (w + ofGameForm q) :=
      h_x_eq (ofGameForm q) ⟨q, hq, rfl⟩
    rw [add_comm (ofGameForm p) x, add_comm (ofGameForm q) x, h_misere_eq_x, h_misere_eq_x',
      add_comm w (ofGameForm p), add_comm w (ofGameForm q)]
    exact h_misere_eq

instance [ShortUniverse U] : Hereditary (ExpansionSet U) where
  has_option := by
    rintro g g' ⟨hs, u, hexp⟩ h2
    rw [IsOption.iff_mem_union, Set.mem_union] at h2
    obtain hg' | hg' := h2
    · have hi := isPlayerExpansion_of_isExpansion hexp .left
      unfold IsPlayerExpansion at hi
      obtain ⟨u', _, hL, hR⟩ := hi.2.1 g' hg'
      exact ⟨Short.of_mem_moves hs hg', u', hL, hR⟩
    · have hi := isPlayerExpansion_of_isExpansion hexp .right
      unfold IsPlayerExpansion at hi
      obtain ⟨u', _, hL, hR⟩ := hi.2.1 g' hg'
      exact ⟨Short.of_mem_moves hs hg', u', hL, hR⟩

instance [ShortUniverse U] : ClosedUnderNeg (ExpansionSet U) where
  neg_of := by
    rintro g ⟨hs, u, hexp⟩
    exact ⟨Short.neg hs, -u, isExpansion_neg U hexp⟩

theorem isExpansion_ofGameForm_dicotic [ShortUniverse U] {B C : Set AugmentedForm.{u}}
    [Small.{u} B] [Small.{u} C]
    (B' C' : Set GameForm.{u}) [Small.{u} B'] [Small.{u} C']
    (hUW : U (!{B' | C'} : GameForm.{u}))
    (hi_left : ∀ b ∈ B, ∃ x ∈ B', IsExpansion U (ofGameForm x) b)
    (hii_left : ∀ x ∈ B', ∃ b ∈ B, IsExpansion U (ofGameForm x) b)
    (hi_right : ∀ c ∈ C, ∃ x ∈ C', IsExpansion U (ofGameForm x) c)
    (hii_right : ∀ x ∈ C', ∃ c ∈ C, IsExpansion U (ofGameForm x) c)
    (hBne : B.Nonempty) (hCne : C.Nonempty) :
    IsExpansion U (ofGameForm (!{B' | C'} : GameForm.{u})) (!{B | C} : AugmentedForm.{u}) := by
  constructor <;> unfold IsPlayerExpansion <;> simp +decide [*]
  · refine ⟨⟨_, hUW, rfl⟩, ?_, ?_, ?_⟩
    · -- (i) every Left option of `!{B | C}` is expanded by some `ofGameForm x`, `x ∈ B'`
      rw [ofGameForm_dicotic, moves_ofSets]
      intro g' hg'
      obtain ⟨x, hx, hexp⟩ := hi_left g' hg'
      exact ⟨ofGameForm x, Set.mem_image_of_mem _ hx, hexp.1, hexp.2⟩
    · -- (ii) conversely, every Left option `ofGameForm x` expands some Left option of `!{B | C}`
      intro _ u' hu'
      obtain ⟨x, hx, rfl⟩ := mem_moves_ofGameForm hu'
      rw [moves_ofSets] at hx
      obtain ⟨b, hb, hbexp⟩ := hii_left x hx
      exact ⟨b, hbexp.1, hb, hbexp.2⟩
    · -- (iii) vacuous: `!{B | C}` has a Left option because `B` is nonempty
      intro h
      rw [isEnd_def, moves_ofSets] at h
      exact absurd h hBne.ne_empty
  · refine ⟨⟨_, hUW, rfl⟩, ?_, ?_, ?_⟩
    · -- (i)
      intro c hc
      obtain ⟨x, hx, hexp⟩ := hi_right c hc
      refine ⟨ofGameForm x, ?_, hexp.1, hexp.2⟩
      rw [ofGameForm_dicotic, moves_ofSets]
      exact Set.mem_image_of_mem _ hx
    · -- (ii)
      intro _ u' hu'
      rw [ofGameForm_dicotic, moves_ofSets] at hu'
      obtain ⟨x, hx, rfl⟩ := hu'
      obtain ⟨c, hc, hcexp⟩ := hii_right x hx
      exact ⟨c, hcexp.1, hc, hcexp.2⟩
    · -- (iii) vacuous: `!{B | C}` has a Right option because `C` is nonempty
      intro h
      rw [isEnd_def, moves_ofSets] at h
      exact absurd h hCne.ne_empty

instance [ShortUniverse U] : ClosedUnderDicotic IsShort (ExpansionSet U) where
  closed_dicotic := by
    intros B C _ _ hB hC hBne hCne hShort
    -- Since `!{B | C}` is short, both `B` and `C` are finite.
    have hB_finite : B.Finite := by
      have h_fin := Short.finite_moves .left hShort
      rw [moves_ofSets] at h_fin
      exact h_fin
    have hC_finite : C.Finite := by
      have h_fin := Short.finite_moves .right hShort
      rw [moves_ofSets] at h_fin
      exact h_fin
    -- Choose, for each `b ∈ B`, a `U`-game `fB b` whose image expands `b`.
    obtain ⟨fB, hfB⟩ : ∃ fB : ↥B → GameForm,
        ∀ b : ↥B, U (fB b) ∧ IsExpansion U (ofGameForm (fB b)) b.1 := by
      have h_choice : ∀ b : ↥B,
          ∃ x : GameForm, U x ∧ IsExpansion U (ofGameForm x) b.1 := by
        intro b
        obtain ⟨_, u, hu⟩ := hB b.1 b.2
        have h_pred := isPlayerExpansion_of_isExpansion hu .left
        unfold IsPlayerExpansion at h_pred
        obtain ⟨x, hx, rfl⟩ := h_pred.1
        exact ⟨x, hx, hu⟩
      exact ⟨fun b => Classical.choose (h_choice b), fun b => Classical.choose_spec (h_choice b)⟩
    -- Similarly, choose `fC c` for each `c ∈ C`.
    obtain ⟨fC, hfC⟩ : ∃ fC : ↥C → GameForm,
        ∀ c : ↥C, U (fC c) ∧ IsExpansion U (ofGameForm (fC c)) c.1 := by
      have h_choice : ∀ c : ↥C,
          ∃ x : GameForm, U x ∧ IsExpansion U (ofGameForm x) c.1 := by
        intro c
        obtain ⟨_, u, hu⟩ := hC c.1 c.2
        have h_pred := isPlayerExpansion_of_isExpansion hu .left
        unfold IsPlayerExpansion at h_pred
        obtain ⟨x, hx, rfl⟩ := h_pred.1
        exact ⟨x, hx, hu⟩
      exact ⟨fun c => Classical.choose (h_choice c), fun c => Classical.choose_spec (h_choice c)⟩
    refine ⟨hShort, _, isExpansion_ofGameForm_dicotic (Set.range fB) (Set.range fC)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    any_goals assumption
    · apply (‹ShortUniverse U›).closed_dicotic
      · rintro _ ⟨b, rfl⟩
        exact hfB b |>.1
      · rintro _ ⟨c, rfl⟩
        exact hfC c |>.1
      · exact ⟨_, ⟨⟨hBne.some, hBne.choose_spec⟩, rfl⟩⟩
      · exact ⟨_, ⟨⟨hCne.some, hCne.choose_spec⟩, rfl⟩⟩
      · apply Short.ofSets
        · convert Set.Finite.image fB (Set.toFinite (Set.univ : Set B)) using 1
          · rw [Set.image_univ]
          · exact Set.finite_univ_iff.mpr hB_finite
        · rintro _ ⟨b, rfl⟩
          exact (‹ShortUniverse U›).isAmbient_of_mem (hfB b |>.1)
        · haveI := hC_finite.to_subtype
          exact Set.toFinite _
        · rintro _ ⟨c, rfl⟩
          exact (‹ShortUniverse U›).isAmbient_of_mem (hfC c |>.1)
    · exact fun b hb => ⟨fB ⟨b, hb⟩, Set.mem_range_self _, hfB ⟨b, hb⟩ |>.2⟩
    · rintro _ ⟨b, rfl⟩
      exact ⟨_, b.2, hfB b |>.2⟩
    · exact fun c hc => ⟨fC ⟨c, hc⟩, Set.mem_range_self _, hfC ⟨c, hc⟩ |>.2⟩
    · rintro _ ⟨c, rfl⟩
      exact ⟨_, c.2, hfC c |>.2⟩

instance [ShortUniverse U] : ShortUniverse (ExpansionSet U) where
  zero_mem := by
    obtain ⟨a, ha, h⟩ : ∃ a : GameForm, U a ∧ ofGameForm a = 0 := by
      exact ⟨0, ‹ShortUniverse U›.zero_mem, ofGameForm_zero⟩
    have := expansionSet_mem_ofGameForm a ha
    rw [h] at this
    exact this
  isAmbient_of_mem := fun hg => hg.1

theorem expansionSet_closedSimplest [ShortUniverse U] (g : AugmentedForm)
    (hg : ExpansionSet U g) :
    ∃ k, ExpansionSet U k ∧ IsShort k ∧ SimplestForm (ExpansionSet U) k ∧
      (k =m (ExpansionSet U) g) := by
  obtain ⟨k, hkShort, hkSimp, hkEq⟩ := exists_simplestForm (U := ExpansionSet U) hg.1
  exact ⟨k, expansionSet_simplestForm_mem hg hkShort hkSimp hkEq, hkShort, hkSimp, hkEq⟩
