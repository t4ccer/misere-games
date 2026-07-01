/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.AugmentedForm.TreeSize
public import CombinatorialGames.Misere.Comparison
public import CombinatorialGames.Misere.Universe

import Mathlib.Algebra.Order.BigOperators.Group.Finset

universe u

public section

open Form
open Form.Misere.Outcome

namespace Form.ComparisonSet

variable {G : Type (u + 1)} [Form G] {U : G → Prop} [ShortUniverse U]

open Form.Misere.Outcome in
theorem misereGE_iff_maintenance_proviso {g h : G} (hg : IsShort g) (hh : IsShort h) :
    g ≥m U h ↔ Maintenance U g h .right ∧ Maintenance U g h .left ∧
      Proviso U g h .right ∧ Proviso U h g .left :=
  letI : Ambient (IsShort (G := G)) := Form.instAmbientIsShort
  (@Form.Promain.of_universe G _ IsShort U Form.instAmbientIsShort inferInstance) hg hh

open Form.Misere.Outcome in
theorem maintenance_proviso_of_misereGE {g h : G} (hg : IsShort g) (hh : IsShort h)
    (hge : g ≥m U h) :
    Maintenance U g h .right ∧ Maintenance U g h .left ∧
      Proviso U g h .right ∧ Proviso U h g .left :=
  letI : Ambient (IsShort (G := G)) := Form.instAmbientIsShort
  ((@Form.Promain.of_universe G _ IsShort U Form.instAmbientIsShort inferInstance) hg hh).mp hge

end Form.ComparisonSet

namespace AugmentedForm

variable {U : AugmentedForm → Prop}

/--
An ordinary Left option $G^{L_1}$ is $\mathcal{U}$-dominated (by $G^{L_2}$) if
$G^{L_1} \le_{\mathcal{U}} G^{L_2}$ for some ordinary Left option $G^{L_2}$.

This is [Siegel (Definition 5.11 on p. 216)][siegel:GeneralDeadendingUniverse:2025] -/
@[expose] def DominatedLeft (A : AugmentedForm → Prop) (g gl₁ : AugmentedForm) : Prop :=
  gl₁ ∈ moves .left g ∧ ∃ gl₂ ∈ moves .left g, gl₂ ≠ gl₁ ∧ (gl₂ ≥m A gl₁)

/--
Eliminate the Left option $G^L$ from $G$.
-/
noncomputable def removeLeftOption (g gl : AugmentedForm) : AugmentedForm :=
  ofSetsWithTombs (fun p => p.casesOn ((moves .left g) \ {gl}) (moves .right g))
    (fun p => g.hasTombstone p)

@[simp] theorem leftMoves_removeLeftOption (g gl₁ : AugmentedForm) :
    moves .left (removeLeftOption g gl₁) = (moves .left g) \ {gl₁} := by
  rw [removeLeftOption, moves_ofSetsWithTombs]

@[simp] theorem rightMoves_removeLeftOption (g gl : AugmentedForm) :
    moves .right (removeLeftOption g gl) = moves .right g := by
  rw [removeLeftOption, moves_ofSetsWithTombs]

@[simp] theorem hasTombstone_removeLeftOption (g gl : AugmentedForm) (p : Player) :
    (removeLeftOption g gl).hasTombstone p ↔ g.hasTombstone p := by
  rw [removeLeftOption, hasTombstone_ofSetsWithTombs]

theorem isShort_removeLeftOption {g : AugmentedForm} (hg : IsShort g) (gl : AugmentedForm) :
    IsShort (removeLeftOption g gl) := by
  refine Short.mk fun p => ⟨?_, ?_⟩
  · cases p <;> simp only [leftMoves_removeLeftOption, rightMoves_removeLeftOption]
    · exact (Short.finite_moves .left hg).subset Set.diff_subset
    · exact Short.finite_moves .right hg
  · cases p <;> intro y hy <;>
      simp only [leftMoves_removeLeftOption, rightMoves_removeLeftOption] at hy
    · exact Short.of_mem_moves hg (Set.mem_of_mem_diff hy)
    · exact Short.of_mem_moves hg hy

theorem treeSize_removeLeftOption_add {g gl : AugmentedForm} (h_short : IsShort g)
    (h_gl_mem : gl ∈ moves .left g) :
    treeSize g = treeSize (removeLeftOption g gl) + treeSize gl := by
  classical
  rw [treeSize_eq h_short, treeSize_eq (isShort_removeLeftOption h_short gl)]
  have h_insert :
      (Short.finite_moves .left h_short).toFinset
      = insert gl (Short.finite_moves .left (isShort_removeLeftOption h_short gl)).toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_insert, leftMoves_removeLeftOption,
               Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · intro h_x_mem
      by_cases h_eq : x = gl
      · exact Or.inl h_eq
      · exact Or.inr ⟨h_x_mem, h_eq⟩
    · rintro (rfl | ⟨hx, _⟩)
      · exact h_gl_mem
      · exact hx
  have h_not_mem :
      gl ∉ (Short.finite_moves .left (isShort_removeLeftOption h_short gl)).toFinset := by
    simp [Set.Finite.mem_toFinset, leftMoves_removeLeftOption]
  have h_removeLeft_eq : (Short.finite_moves .right h_short).toFinset
      = (Short.finite_moves .right (isShort_removeLeftOption h_short gl)).toFinset := by
    simp only [rightMoves_removeLeftOption]
  rw [h_insert, Finset.sum_insert h_not_mem, h_removeLeft_eq,
    hasTombstone_removeLeftOption, hasTombstone_removeLeftOption]
  ac_rfl

theorem treeSize_removeLeftOption_lt {g gl : AugmentedForm} (hg : IsShort g)
    (h_gl_mem : gl ∈ moves .left g) :
    treeSize (removeLeftOption g gl) < treeSize g := by
  rw [treeSize_removeLeftOption_add hg h_gl_mem]
  exact lt_add_of_pos_right _
    (lt_of_lt_of_le zero_lt_one (one_le_treeSize (Short.of_mem_moves hg h_gl_mem)))

/--
Eliminating a dominated Left option preserves $\mathcal{U}$-equivalence.

This is [Siegel (Lemma 5.12 on p. 216)][siegel:GeneralDeadendingUniverse:2025]
-/
theorem removeLeftOption_misereEQ [Hereditary U] {g gl₁ : AugmentedForm}
    (h_dom : DominatedLeft U g gl₁) : (removeLeftOption g gl₁) =m U g := by
  obtain ⟨h_gl₁_mem, gl₂, h_gl₂_mem, h_gl₂_ne, hgl₂ge⟩ := h_dom
  apply MisereEq.of_antisymm
  · apply Hereditary.misereGE_of_maintenance_proviso
    · intro gr hgr
      rw [rightMoves_removeLeftOption] at hgr
      exact Or.inl ⟨gr, hgr, MisereGE.refl _⟩
    · intro hl hhl
      by_cases hne : hl = gl₁
      · subst hne
        refine Or.inl ⟨gl₂, ?_, hgl₂ge⟩
        rw [leftMoves_removeLeftOption]
        exact ⟨h_gl₂_mem, h_gl₂_ne⟩
      · refine Or.inl ⟨hl, ?_, MisereGE.refl _⟩
        rw [leftMoves_removeLeftOption]
        exact ⟨hhl, hne⟩
    · intro hend
      apply strong_of_isEndLike
      rw [IsEndLike_iff, isEnd_def]
      rw [IsEndLike_iff, hasTombstone_removeLeftOption, isEnd_def,
        rightMoves_removeLeftOption] at hend
      exact hend
    · intro hend
      apply strong_of_isEndLike
      rw [IsEndLike_iff] at hend
      rw [IsEndLike_iff, hasTombstone_removeLeftOption]
      rcases hend with htomb | hisend
      · exact Or.inl htomb
      · exact absurd hisend (not_isEnd_of_mem_moves h_gl₁_mem)
  · apply Hereditary.misereGE_of_maintenance_proviso
    · intro gr hgr
      refine Or.inl ⟨gr, ?_, MisereGE.refl _⟩
      rw [rightMoves_removeLeftOption]; exact hgr
    · intro hl hhl
      rw [leftMoves_removeLeftOption] at hhl
      exact Or.inl ⟨hl, hhl.1, MisereGE.refl _⟩
    · intro hend
      apply strong_of_isEndLike
      rw [IsEndLike_iff, hasTombstone_removeLeftOption, isEnd_def,
        rightMoves_removeLeftOption]
      rw [IsEndLike_iff, isEnd_def] at hend
      exact hend
    · intro hend
      apply strong_of_isEndLike
      rw [IsEndLike_iff] at hend
      rw [IsEndLike_iff]
      rcases hend with htomb | hisend
      · exact Or.inl ((hasTombstone_removeLeftOption g gl₁ .left).mp htomb)
      · rw [isEnd_def, leftMoves_removeLeftOption] at hisend
        have hmem : gl₂ ∈ moves .left g \ {gl₁} := ⟨h_gl₂_mem, h_gl₂_ne⟩
        rw [hisend] at hmem
        exact ((Set.mem_empty_iff_false gl₂).mp hmem).elim

/--
An ordinary Left option $G^{L_1}$ is $\mathcal{U}$-reversible (through $G^{L_1 R_1}$) if
$G \ge_{\mathcal{U}} G^{L_1 R_1}$ for some ordinary Right option $G^{L_1 R_1}$.

This is [Siegel (Definition 5.11 on p. 216)][siegel:GeneralDeadendingUniverse:2025] -/
@[expose] def ReversibleLeftThrough (A : AugmentedForm → Prop)
    (g gl glr : AugmentedForm) : Prop :=
  gl ∈ moves .left g ∧ glr ∈ moves .right gl ∧ (g ≥m A glr)

noncomputable def openBypassLeft (g gl₁ glr₁ : AugmentedForm) : AugmentedForm :=
  haveI : Small.{u} ↥(((moves .left g) \ {gl₁}) ∪ moves .left glr₁) := inferInstance
  ofSetsWithTombs
    (fun p => p.casesOn (((moves .left g) \ {gl₁}) ∪ moves .left glr₁) (moves .right g))
    (fun p => p.casesOn (g.hasTombstone .left ∨ glr₁.hasTombstone .left) (g.hasTombstone .right))

@[simp] theorem leftMoves_openBypassLeft (g gl₁ glr₁ : AugmentedForm) :
    moves .left (openBypassLeft g gl₁ glr₁) = ((moves .left g) \ {gl₁}) ∪ moves .left glr₁ := by
  rw [openBypassLeft, moves_ofSetsWithTombs]

@[simp] theorem rightMoves_openBypassLeft (g gl₁ glr₁ : AugmentedForm) :
    moves .right (openBypassLeft g gl₁ glr₁) = moves .right g := by
  rw [openBypassLeft, moves_ofSetsWithTombs]

@[simp] theorem hasTombstone_left_openBypassLeft (g gl₁ glr₁ : AugmentedForm) :
    (openBypassLeft g gl₁ glr₁).hasTombstone .left ↔
      (g.hasTombstone .left ∨ glr₁.hasTombstone .left) := by
  rw [openBypassLeft, hasTombstone_ofSetsWithTombs]

@[simp] theorem hasTombstone_right_openBypassLeft (g gl₁ glr₁ : AugmentedForm) :
    (openBypassLeft g gl₁ glr₁).hasTombstone .right ↔ g.hasTombstone .right := by
  rw [openBypassLeft, hasTombstone_ofSetsWithTombs]

theorem isShort_openBypassLeft {g gl₁ glr₁ : AugmentedForm}
    (hg : IsShort g) (hglr : IsShort glr₁) :
    IsShort (openBypassLeft g gl₁ glr₁) := by
  refine Short.mk fun p => ⟨?_, ?_⟩
  · cases p <;> simp only [leftMoves_openBypassLeft, rightMoves_openBypassLeft]
    · exact ((Short.finite_moves .left hg).subset Set.diff_subset).union
        (Short.finite_moves .left hglr)
    · exact Short.finite_moves .right hg
  · cases p <;> intro y hy <;>
      simp only [leftMoves_openBypassLeft, rightMoves_openBypassLeft] at hy
    · rcases hy with hy | hy
      · exact Short.of_mem_moves hg (Set.mem_of_mem_diff hy)
      · exact Short.of_mem_moves hglr hy
    · exact Short.of_mem_moves hg hy

theorem treeSize_openBypassLeft_le {g gl₁ glr₁ : AugmentedForm} (hg : IsShort g)
    (hglrS : IsShort glr₁) :
    treeSize (openBypassLeft g gl₁ glr₁) ≤
      treeSize (removeLeftOption g gl₁) + 1
        + (∑ x ∈ (Short.finite_moves .left hglrS).toFinset, treeSize x) := by
  classical
  rw [treeSize_eq (isShort_openBypassLeft (gl₁ := gl₁) hg hglrS),
    treeSize_eq (isShort_removeLeftOption hg gl₁)]
  have hLB : (Short.finite_moves .left (isShort_openBypassLeft (gl₁ := gl₁) hg hglrS)).toFinset
      = (Short.finite_moves .left (isShort_removeLeftOption hg gl₁)).toFinset
        ∪ (Short.finite_moves .left hglrS).toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_union, leftMoves_openBypassLeft,
      leftMoves_removeLeftOption, Set.mem_union]
  have hRB : (Short.finite_moves .right (isShort_openBypassLeft (gl₁ := gl₁) hg hglrS)).toFinset
      = (Short.finite_moves .right (isShort_removeLeftOption hg gl₁)).toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset, rightMoves_openBypassLeft, rightMoves_removeLeftOption]
  rw [hLB, hRB]
  have htR : ((openBypassLeft g gl₁ glr₁).hasTombstone .right)
      = ((removeLeftOption g gl₁).hasTombstone .right) := by
    simp only [hasTombstone_right_openBypassLeft, hasTombstone_removeLeftOption]
  rw [htR]
  set A := (Short.finite_moves .left (isShort_removeLeftOption hg gl₁)).toFinset with hA
  set B := (Short.finite_moves .left hglrS).toFinset with hB
  set rR := ∑ x ∈ (Short.finite_moves .right (isShort_removeLeftOption hg gl₁)).toFinset,
    treeSize x with hrR
  have hunion : (∑ x ∈ A ∪ B, treeSize x) ≤ (∑ x ∈ A, treeSize x) + (∑ x ∈ B, treeSize x) :=
    calc (∑ x ∈ A ∪ B, treeSize x)
        ≤ (∑ x ∈ A ∪ B, treeSize x) + ∑ x ∈ A ∩ B, treeSize x := NatOrdinal.le_add_right
      _ = (∑ x ∈ A, treeSize x) + (∑ x ∈ B, treeSize x) := Finset.sum_union_inter
  have htL :
      (if (openBypassLeft g gl₁ glr₁).hasTombstone .left then (1:NatOrdinal) else 0) ≤ 1 := by
    split_ifs
    · exact le_refl 1
    · exact NatOrdinal.zero_le 1
  calc (if (openBypassLeft g gl₁ glr₁).hasTombstone .left then (1:NatOrdinal) else 0)
        + (if (removeLeftOption g gl₁).hasTombstone .right then 1 else 0) + 1
        + (∑ x ∈ A ∪ B, treeSize x) + rR
      ≤ 1 + (if (removeLeftOption g gl₁).hasTombstone .right then 1 else 0) + 1
        + ((∑ x ∈ A, treeSize x) + (∑ x ∈ B, treeSize x)) + rR := by
        gcongr
    _ ≤ ((if (removeLeftOption g gl₁).hasTombstone .left then 1 else 0)
          + (if (removeLeftOption g gl₁).hasTombstone .right then 1 else 0) + 1
          + (∑ x ∈ A, treeSize x) + rR) + 1 + (∑ x ∈ B, treeSize x) := by
        have e : ((if (removeLeftOption g gl₁).hasTombstone .left then (1:NatOrdinal) else 0)
              + (if (removeLeftOption g gl₁).hasTombstone .right then 1 else 0) + 1
              + (∑ x ∈ A, treeSize x) + rR) + 1 + (∑ x ∈ B, treeSize x)
            = (if (removeLeftOption g gl₁).hasTombstone .left then 1 else 0)
              + (1 + (if (removeLeftOption g gl₁).hasTombstone .right then 1 else 0) + 1
                + ((∑ x ∈ A, treeSize x) + (∑ x ∈ B, treeSize x)) + rR) := by ac_rfl
        rw [e]
        exact NatOrdinal.le_add_left

theorem treeSize_openBypassLeft_lt {g gl₁ glr₁ : AugmentedForm} (hg : IsShort g)
    (hgl : gl₁ ∈ moves .left g) (hglr : glr₁ ∈ moves .right gl₁) :
    treeSize (openBypassLeft g gl₁ glr₁) < treeSize g := by
  have hgls : IsShort gl₁ := Short.of_mem_moves hg hgl
  have hglrS : IsShort glr₁ := Short.of_mem_moves hgls hglr
  have hsum := sum_leftMoves_add_one_le hglrS
  have hgl_ge : (1 : NatOrdinal) + treeSize glr₁ ≤ treeSize gl₁ := by
    classical
    have hsr : treeSize glr₁ ≤ ∑ x ∈ (Short.finite_moves .right hgls).toFinset, treeSize x :=
      Finset.single_le_sum (fun x _ => NatOrdinal.zero_le _) ((Set.Finite.mem_toFinset _).2 hglr)
    rw [treeSize_eq hgls]
    set sL := ∑ x ∈ (Short.finite_moves .left hgls).toFinset, treeSize x with hsL
    set sR := ∑ x ∈ (Short.finite_moves .right hgls).toFinset, treeSize x with hsR
    calc (1 : NatOrdinal) + treeSize glr₁ ≤ 1 + sR := add_le_add le_rfl hsr
      _ ≤ (if gl₁.hasTombstone .left then 1 else 0)
            + (if gl₁.hasTombstone .right then 1 else 0) + 1 + sL + sR := by
          have e : (if gl₁.hasTombstone .left then (1:NatOrdinal) else 0)
                + (if gl₁.hasTombstone .right then 1 else 0) + 1 + sL + sR
              = (1 + sR) + ((if gl₁.hasTombstone .left then 1 else 0)
                  + (if gl₁.hasTombstone .right then 1 else 0) + sL) := by ac_rfl
          rw [e]; exact NatOrdinal.le_add_right
  have hkey : (1 : NatOrdinal)
        + (∑ x ∈ (Short.finite_moves .left hglrS).toFinset, treeSize x) < treeSize gl₁ := by
    have hlt : (∑ x ∈ (Short.finite_moves .left hglrS).toFinset, treeSize x) < treeSize glr₁ :=
      lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) hsum
    exact lt_of_lt_of_le (add_lt_add_of_le_of_lt le_rfl hlt) hgl_ge
  calc treeSize (openBypassLeft g gl₁ glr₁)
      ≤ treeSize (removeLeftOption g gl₁) + 1
        + (∑ x ∈ (Short.finite_moves .left hglrS).toFinset, treeSize x) :=
        treeSize_openBypassLeft_le (gl₁ := gl₁) hg hglrS
    _ = treeSize (removeLeftOption g gl₁)
        + (1 + (∑ x ∈ (Short.finite_moves .left hglrS).toFinset, treeSize x)) := by
        rw [add_assoc]
    _ < treeSize (removeLeftOption g gl₁) + treeSize gl₁ := add_lt_add_of_le_of_lt le_rfl hkey
    _ = treeSize g := (treeSize_removeLeftOption_add hg hgl).symm

/--
Bypassing an open reversible Left option preserves $\mathcal{U}$-equivalence.

This is [Siegel (Lemma 5.13 on p. 217)][siegel:GeneralDeadendingUniverse:2025]
-/
theorem openBypassLeft_misereEQ [ShortUniverse U] {g gl₁ glr₁ : AugmentedForm} (hg : IsShort g)
    (h : ReversibleLeftThrough U g gl₁ glr₁) (hne : ¬ IsEnd .left glr₁) :
    (openBypassLeft g gl₁ glr₁) =m U g := by
  obtain ⟨hgl₁mem, hglr₁mem, hge⟩ := h
  have hglr : IsShort glr₁ :=
    Short.of_mem_moves (Short.of_mem_moves hg hgl₁mem) hglr₁mem
  have hg' : IsShort (openBypassLeft g gl₁ glr₁) :=
    isShort_openBypassLeft hg hglr
  obtain ⟨hMr, hMl, hPr, hPl⟩ :=
    Form.ComparisonSet.maintenance_proviso_of_misereGE hg hglr hge
  have hsub : openBypassLeft g gl₁ glr₁ ≥m U glr₁ := by
    refine (Form.ComparisonSet.misereGE_iff_maintenance_proviso hg' hglr).mpr ⟨?_, ?_, ?_, ?_⟩
    · intro gr hgr
      rw [rightMoves_openBypassLeft] at hgr
      exact hMr gr hgr
    · intro x hx
      refine Or.inl ⟨x, ?_, MisereGE.refl _⟩
      rw [leftMoves_openBypassLeft]; exact Or.inr hx
    · intro hend
      apply hPr
      rw [IsEndLike_iff, isEnd_def]
      rw [IsEndLike_iff, hasTombstone_right_openBypassLeft, isEnd_def,
        rightMoves_openBypassLeft] at hend
      exact hend
    · intro hend
      apply strong_of_isEndLike
      rw [IsEndLike_iff] at hend
      rw [IsEndLike_iff, hasTombstone_left_openBypassLeft]
      rcases hend with htomb | hisend
      · exact Or.inl (Or.inr htomb)
      · exact absurd hisend hne
  apply MisereEq.of_antisymm
  · refine (Form.ComparisonSet.misereGE_iff_maintenance_proviso hg' hg).mpr ⟨?_, ?_, ?_, ?_⟩
    · intro gr hgr
      rw [rightMoves_openBypassLeft] at hgr
      exact Or.inl ⟨gr, hgr, MisereGE.refl _⟩
    · intro hl hhl
      by_cases hne' : hl = gl₁
      · subst hne'
        exact Or.inr ⟨glr₁, hglr₁mem, hsub⟩
      · refine Or.inl ⟨hl, ?_, MisereGE.refl _⟩
        rw [leftMoves_openBypassLeft]; exact Or.inl ⟨hhl, hne'⟩
    · intro hend
      apply strong_of_isEndLike
      rw [IsEndLike_iff, isEnd_def]
      rw [IsEndLike_iff, hasTombstone_right_openBypassLeft, isEnd_def,
        rightMoves_openBypassLeft] at hend
      exact hend
    · intro hend
      apply strong_of_isEndLike
      rw [IsEndLike_iff] at hend
      rw [IsEndLike_iff, hasTombstone_left_openBypassLeft]
      rcases hend with htomb | hisend
      · exact Or.inl (Or.inl htomb)
      · exact absurd hisend (not_isEnd_of_mem_moves hgl₁mem)
  · refine (Form.ComparisonSet.misereGE_iff_maintenance_proviso hg hg').mpr ⟨?_, ?_, ?_, ?_⟩
    · intro gr hgr
      refine Or.inl ⟨gr, ?_, MisereGE.refl _⟩
      rw [rightMoves_openBypassLeft]; exact hgr
    · intro hl hhl
      rw [leftMoves_openBypassLeft] at hhl
      rcases hhl with ⟨hhlmem, hhlne⟩ | hhlglr
      · exact Or.inl ⟨hl, hhlmem, MisereGE.refl _⟩
      · exact hMl hl hhlglr
    · intro hend
      apply strong_of_isEndLike
      rw [IsEndLike_iff, hasTombstone_right_openBypassLeft, isEnd_def,
        rightMoves_openBypassLeft]
      rw [IsEndLike_iff, isEnd_def] at hend
      exact hend
    · intro hend
      rw [IsEndLike_iff, hasTombstone_left_openBypassLeft] at hend
      rcases hend with (htombg | htombglr) | hisend
      · exact strong_of_isEndLike (by rw [IsEndLike_iff]; exact Or.inl htombg)
      · exact hPl (by rw [IsEndLike_iff]; exact Or.inl htombglr)
      · rw [isEnd_def, leftMoves_openBypassLeft, Set.union_empty_iff] at hisend
        exact absurd (by rw [isEnd_def]; exact hisend.2) hne

-- TODO: Rename "atomic reversibility" to "end reversibility"

noncomputable def atomicReplaceLeft (g gl₁ : AugmentedForm) : AugmentedForm :=
  haveI : Small.{u} ↥((moves .left g) \ {gl₁}) := small_subset Set.diff_subset
  ofSetsWithTombs (fun p => p.casesOn ((moves .left g) \ {gl₁}) (moves .right g))
    (fun p => p.casesOn True (g.hasTombstone .right))

@[simp] theorem leftMoves_atomicReplaceLeft (g gl₁ : AugmentedForm) :
    moves .left (atomicReplaceLeft g gl₁) = (moves .left g) \ {gl₁} := by
  rw [atomicReplaceLeft, moves_ofSetsWithTombs]

@[simp] theorem rightMoves_atomicReplaceLeft (g gl₁ : AugmentedForm) :
    moves .right (atomicReplaceLeft g gl₁) = moves .right g := by
  rw [atomicReplaceLeft, moves_ofSetsWithTombs]

@[simp] theorem hasTombstone_left_atomicReplaceLeft (g gl₁ : AugmentedForm) :
    (atomicReplaceLeft g gl₁).hasTombstone .left := by
  rw [atomicReplaceLeft, hasTombstone_ofSetsWithTombs]; exact trivial

@[simp] theorem hasTombstone_right_atomicReplaceLeft (g gl₁ : AugmentedForm) :
    (atomicReplaceLeft g gl₁).hasTombstone .right ↔ g.hasTombstone .right := by
  rw [atomicReplaceLeft, hasTombstone_ofSetsWithTombs]

theorem isShort_atomicReplaceLeft {g gl₁ : AugmentedForm} (hg : IsShort g) :
    IsShort (atomicReplaceLeft g gl₁) := by
  refine Short.mk fun p => ⟨?_, ?_⟩
  · cases p <;> simp only [leftMoves_atomicReplaceLeft, rightMoves_atomicReplaceLeft]
    · exact (Short.finite_moves .left hg).subset Set.diff_subset
    · exact Short.finite_moves .right hg
  · cases p <;> intro y hy <;>
      simp only [leftMoves_atomicReplaceLeft, rightMoves_atomicReplaceLeft] at hy
    · exact Short.of_mem_moves hg (Set.mem_of_mem_diff hy)
    · exact Short.of_mem_moves hg hy

theorem treeSize_atomicReplaceLeft_le {g gl₁ : AugmentedForm} (hg : IsShort g) :
    treeSize (atomicReplaceLeft g gl₁) ≤ treeSize (removeLeftOption g gl₁) + 1 := by
  classical
  have hL : (Short.finite_moves .left (isShort_atomicReplaceLeft (gl₁ := gl₁) hg)).toFinset
      = (Short.finite_moves .left (isShort_removeLeftOption hg gl₁)).toFinset := by
    ext x; simp only [Set.Finite.mem_toFinset, leftMoves_atomicReplaceLeft,
      leftMoves_removeLeftOption]
  have hR : (Short.finite_moves .right (isShort_atomicReplaceLeft (gl₁ := gl₁) hg)).toFinset
      = (Short.finite_moves .right (isShort_removeLeftOption hg gl₁)).toFinset := by
    ext x; simp only [Set.Finite.mem_toFinset, rightMoves_atomicReplaceLeft,
      rightMoves_removeLeftOption]
  have hkey : treeSize (atomicReplaceLeft g gl₁)
        + (if g.hasTombstone .left then (1:NatOrdinal) else 0)
      = treeSize (removeLeftOption g gl₁) + 1 := by
    rw [treeSize_eq (isShort_atomicReplaceLeft (gl₁ := gl₁) hg),
      treeSize_eq (isShort_removeLeftOption hg gl₁), hL, hR,
      if_pos (hasTombstone_left_atomicReplaceLeft g gl₁)]
    simp only [hasTombstone_right_atomicReplaceLeft, hasTombstone_removeLeftOption]
    ac_rfl
  rw [← hkey]
  exact NatOrdinal.le_add_right

theorem treeSize_atomicReplaceLeft_lt {g gl₁ glr₁ : AugmentedForm} (hg : IsShort g)
    (hgl : gl₁ ∈ moves .left g) (hglr : glr₁ ∈ moves .right gl₁) :
    treeSize (atomicReplaceLeft g gl₁) < treeSize g := by
  have hgls : IsShort gl₁ := Short.of_mem_moves hg hgl
  have h2 : (1 : NatOrdinal) < treeSize gl₁ := by
    classical
    have h1R : (0 : NatOrdinal) < ∑ x ∈ (Short.finite_moves .right hgls).toFinset, treeSize x :=
      lt_of_lt_of_le zero_lt_one (le_trans (one_le_treeSize (Short.of_mem_moves hgls hglr))
        (Finset.single_le_sum (fun x _ => NatOrdinal.zero_le _)
          ((Set.Finite.mem_toFinset _).2 hglr)))
    rw [treeSize_eq hgls]
    set sL := ∑ x ∈ (Short.finite_moves .left hgls).toFinset, treeSize x with hsL
    set sR := ∑ x ∈ (Short.finite_moves .right hgls).toFinset, treeSize x with hsR
    have e : (if gl₁.hasTombstone .left then (1 : NatOrdinal) else 0)
          + (if gl₁.hasTombstone .right then 1 else 0) + 1 + sL + sR
        = (1 + sR) + ((if gl₁.hasTombstone .left then 1 else 0)
            + (if gl₁.hasTombstone .right then 1 else 0) + sL) := by ac_rfl
    rw [e]
    exact lt_of_lt_of_le (lt_add_of_pos_right 1 h1R) NatOrdinal.le_add_right
  calc treeSize (atomicReplaceLeft g gl₁)
      ≤ treeSize (removeLeftOption g gl₁) + 1 := treeSize_atomicReplaceLeft_le (gl₁ := gl₁) hg
    _ < treeSize (removeLeftOption g gl₁) + treeSize gl₁ := add_lt_add_of_le_of_lt le_rfl h2
    _ = treeSize g := (treeSize_removeLeftOption_add hg hgl).symm

/--
Replacing an atomic reversible Left option by a tombstone preserves $\mathcal{U}$-equivalence.

This is [Siegel (Lemma 5.14 on p. 217)][siegel:GeneralDeadendingUniverse:2025]
-/
theorem atomicReplaceLeft_misereEQ [ShortUniverse U] {g gl₁ glr₁ : AugmentedForm} (hg : IsShort g)
    (h : ReversibleLeftThrough U g gl₁ glr₁) (hend : IsEnd .left glr₁) :
    (atomicReplaceLeft g gl₁) =m U g := by
  obtain ⟨hgl₁, hglr₁, hge⟩ := h
  have hglr : IsShort glr₁ := Short.of_mem_moves (Short.of_mem_moves hg hgl₁) hglr₁
  have har : IsShort (atomicReplaceLeft g gl₁) := isShort_atomicReplaceLeft hg
  obtain ⟨hMr, _, hPr, _⟩ :=
    Form.ComparisonSet.maintenance_proviso_of_misereGE hg hglr hge
  have h_subclaim : atomicReplaceLeft g gl₁ ≥m U glr₁ := by
    refine (Form.ComparisonSet.misereGE_iff_maintenance_proviso har hglr).mpr ⟨?_, ?_, ?_, ?_⟩
    · intro gr hgr
      rw [rightMoves_atomicReplaceLeft] at hgr
      exact hMr gr hgr
    · intro hl hhl
      have he := hend; rw [isEnd_def] at he; rw [he] at hhl
      exact ((Set.mem_empty_iff_false hl).mp hhl).elim
    · intro hend'
      apply hPr
      rw [IsEndLike_iff, isEnd_def]
      rw [IsEndLike_iff, hasTombstone_right_atomicReplaceLeft, isEnd_def,
        rightMoves_atomicReplaceLeft] at hend'
      exact hend'
    · intro _
      exact strong_of_isEndLike (Or.inl (hasTombstone_left_atomicReplaceLeft g gl₁))
  apply MisereEq.of_antisymm
  · refine (Form.ComparisonSet.misereGE_iff_maintenance_proviso har hg).mpr ⟨?_, ?_, ?_, ?_⟩
    · intro gr hgr
      rw [rightMoves_atomicReplaceLeft] at hgr
      exact Or.inl ⟨gr, hgr, MisereGE.refl _⟩
    · intro hl hhl
      by_cases hne' : hl = gl₁
      · subst hne'
        exact Or.inr ⟨glr₁, hglr₁, h_subclaim⟩
      · refine Or.inl ⟨hl, ?_, MisereGE.refl _⟩
        rw [leftMoves_atomicReplaceLeft]; exact ⟨hhl, hne'⟩
    · intro hend'
      apply strong_of_isEndLike
      rw [IsEndLike_iff, isEnd_def]
      rw [IsEndLike_iff, hasTombstone_right_atomicReplaceLeft, isEnd_def,
        rightMoves_atomicReplaceLeft] at hend'
      exact hend'
    · intro _
      exact strong_of_isEndLike (Or.inl (hasTombstone_left_atomicReplaceLeft g gl₁))
  · refine (Form.ComparisonSet.misereGE_iff_maintenance_proviso hg har).mpr ⟨?_, ?_, ?_, ?_⟩
    · intro gr hgr
      refine Or.inl ⟨gr, ?_, MisereGE.refl _⟩
      rw [rightMoves_atomicReplaceLeft]; exact hgr
    · intro hl hhl
      rw [leftMoves_atomicReplaceLeft] at hhl
      exact Or.inl ⟨hl, hhl.1, MisereGE.refl _⟩
    · intro hend'
      apply strong_of_isEndLike
      rw [IsEndLike_iff, hasTombstone_right_atomicReplaceLeft, isEnd_def,
        rightMoves_atomicReplaceLeft]
      rw [IsEndLike_iff, isEnd_def] at hend'
      exact hend'
    · intro _
      exact proviso_left_of_misereGE hge (isEndLike_of_isEnd hend)

/--
Erase a Left tombstone from $G$

This is [Siegel (Definition 5.15 on p. 218)][siegel:GeneralDeadendingUniverse:2025]
-/
noncomputable def eraseLeftTomb (g : AugmentedForm) : AugmentedForm :=
  ofSetsWithTombs (fun p => moves p g) (fun p => p.casesOn False (g.hasTombstone .right))

@[simp] theorem moves_eraseLeftTomb (g : AugmentedForm) (p : Player) :
    moves p (eraseLeftTomb g) = moves p g := by
  rw [eraseLeftTomb, moves_ofSetsWithTombs]

@[simp] theorem hasTombstone_left_eraseLeftTomb (g : AugmentedForm) :
    ¬ (eraseLeftTomb g).hasTombstone .left := by
  rw [eraseLeftTomb, hasTombstone_ofSetsWithTombs]; exact id

@[simp] theorem hasTombstone_right_eraseLeftTomb (g : AugmentedForm) :
    (eraseLeftTomb g).hasTombstone .right ↔ g.hasTombstone .right := by
  rw [eraseLeftTomb, hasTombstone_ofSetsWithTombs]

theorem isShort_eraseLeftTomb {g : AugmentedForm} (hg : IsShort g) :
    IsShort (eraseLeftTomb g) := by
  refine Short.mk fun p => ⟨?_, ?_⟩
  · simp only [moves_eraseLeftTomb]; exact Short.finite_moves p hg
  · intro y hy; simp only [moves_eraseLeftTomb] at hy; exact Short.of_mem_moves hg hy

theorem treeSize_eraseLeftTomb_eq {g : AugmentedForm} (hg : IsShort g)
    (htomb : g.hasTombstone .left) :
    treeSize g = treeSize (eraseLeftTomb g) + 1 := by
  classical
  rw [treeSize_eq hg, treeSize_eq (isShort_eraseLeftTomb hg)]
  have hL : (Short.finite_moves .left (isShort_eraseLeftTomb hg)).toFinset
      = (Short.finite_moves .left hg).toFinset := by
    ext x; simp only [Set.Finite.mem_toFinset, moves_eraseLeftTomb]
  have hR : (Short.finite_moves .right (isShort_eraseLeftTomb hg)).toFinset
      = (Short.finite_moves .right hg).toFinset := by
    ext x; simp only [Set.Finite.mem_toFinset, moves_eraseLeftTomb]
  rw [hL, hR, hasTombstone_right_eraseLeftTomb, if_pos htomb]
  simp only [hasTombstone_left_eraseLeftTomb, if_false]
  ac_rfl

theorem treeSize_eraseLeftTomb_lt {g : AugmentedForm} (hg : IsShort g)
    (h_tomb : g.hasTombstone .left) :
    treeSize (eraseLeftTomb g) < treeSize g := by
  rw [treeSize_eraseLeftTomb_eq hg h_tomb]
  exact lt_add_of_pos_right _ zero_lt_one

/--
Erasing a Left tombstone whose erasure is still Left $\mathcal{U}$-strong
preserves $\mathcal{U}$-equivalence.

This is [Siegel (Lemma 5.16 on p. 218)][siegel:GeneralDeadendingUniverse:2025]
-/
theorem eraseLeftTomb_misereEQ [Hereditary U] {g : AugmentedForm} (hg : IsShort g)
    (h_g_tomb : g.hasTombstone .left) (h_erase_strong : Strong U (eraseLeftTomb g) .left) :
    (eraseLeftTomb g) =m U g := by
  have hel : IsShort (eraseLeftTomb g) := isShort_eraseLeftTomb hg
  apply MisereEq.of_antisymm
  · apply Hereditary.misereGE_of_maintenance_proviso
    · intro gr h_gr_mem
      rw [moves_eraseLeftTomb] at h_gr_mem
      exact Or.inl ⟨gr, h_gr_mem, MisereGE.refl _⟩
    · intro hl h_hl_mem
      refine Or.inl ⟨hl, ?_, MisereGE.refl _⟩
      rw [moves_eraseLeftTomb]; exact h_hl_mem
    · intro h_end
      apply strong_of_isEndLike
      rw [IsEndLike_iff, isEnd_def]
      rwa [IsEndLike_iff, hasTombstone_right_eraseLeftTomb, isEnd_def, moves_eraseLeftTomb] at h_end
    · intro _
      exact h_erase_strong
  · apply Hereditary.misereGE_of_maintenance_proviso
    · intro gr h_gr_mem
      refine Or.inl ⟨gr, ?_, MisereGE.refl _⟩
      rw [moves_eraseLeftTomb]; exact h_gr_mem
    · intro hl h_hl_mem
      rw [moves_eraseLeftTomb] at h_hl_mem
      exact Or.inl ⟨hl, h_hl_mem, MisereGE.refl _⟩
    · intro h_end
      apply strong_of_isEndLike
      rw [IsEndLike_iff, hasTombstone_right_eraseLeftTomb, isEnd_def, moves_eraseLeftTomb]
      rwa [IsEndLike_iff, isEnd_def] at h_end
    · intro _
      exact strong_of_isEndLike (Or.inl h_g_tomb)

@[expose] def DominatedRight (A : AugmentedForm → Prop) (g gr₁ : AugmentedForm) : Prop :=
  gr₁ ∈ moves .right g ∧ ∃ gr₂ ∈ moves .right g, gr₂ ≠ gr₁ ∧ (gr₁ ≥m A gr₂)

theorem dominatedRight_iff_neg [ClosedUnderNeg U] {g gr : AugmentedForm} :
    DominatedRight U g gr ↔ DominatedLeft U (-g) (-gr) := by
  unfold DominatedRight DominatedLeft
  simp [moves_neg]

@[expose] def ReversibleRightThrough (A : AugmentedForm → Prop)
    (g gr grl : AugmentedForm) : Prop :=
  gr ∈ moves .right g ∧ grl ∈ moves .left gr ∧ (grl ≥m A g)

theorem reversibleRight_iff_neg [ClosedUnderNeg U] {g gr grl : AugmentedForm} :
    ReversibleRightThrough U g gr grl ↔ ReversibleLeftThrough U (-g) (-gr) (-grl) := by
  unfold ReversibleRightThrough ReversibleLeftThrough
  simp [moves_neg, Set.mem_neg, ClosedUnderNeg.neg_ge_neg_iff]

noncomputable def eraseRightTomb (g : AugmentedForm) : AugmentedForm :=
  ofSetsWithTombs (fun p => moves p g) (fun p => p.casesOn (g.hasTombstone .left) False)

@[simp] theorem moves_eraseRightTomb (g : AugmentedForm) (p : Player) :
    moves p (eraseRightTomb g) = moves p g := by
  rw [eraseRightTomb, moves_ofSetsWithTombs]

@[simp] theorem hasTombstone_right_eraseRightTomb (g : AugmentedForm) :
    ¬ (eraseRightTomb g).hasTombstone .right := by
  rw [eraseRightTomb, hasTombstone_ofSetsWithTombs]; exact id

@[simp] theorem hasTombstone_left_eraseRightTomb (g : AugmentedForm) :
    (eraseRightTomb g).hasTombstone .left ↔ g.hasTombstone .left := by
  rw [eraseRightTomb, hasTombstone_ofSetsWithTombs]

theorem isShort_eraseRightTomb {g : AugmentedForm} (hg : IsShort g) :
    IsShort (eraseRightTomb g) := by
  apply Short.mk
  intro p
  constructor
  · simp only [moves_eraseRightTomb]
    exact Short.finite_moves p hg
  · intro y hy
    simp only [moves_eraseRightTomb] at hy
    exact Short.of_mem_moves hg hy

theorem eraseRightTomb_eq_neg (g : AugmentedForm) :
    eraseRightTomb g = -(eraseLeftTomb (-g)) := by
  apply ext
  · intro p
    simp only [moves_neg, moves_eraseLeftTomb, moves_eraseRightTomb, neg_neg]
  · intro p
    rw [hasTombstone_neg_iff]
    cases p <;> simp [hasTombstone_neg_iff]

@[expose] def NoDominated (A : AugmentedForm → Prop) (g : AugmentedForm) : Prop :=
  (¬ ∃ gl, DominatedLeft A g gl) ∧ (¬ ∃ gr, DominatedRight A g gr)

@[expose] def NoReversible (A : AugmentedForm → Prop) (g : AugmentedForm) : Prop :=
  (¬ ∃ gl glr, ReversibleLeftThrough A g gl glr) ∧
    (¬ ∃ gr grl, ReversibleRightThrough A g gr grl)

/--
$G$ is not erasable for either player if it has a tombstone
and erasing it would stop $G$ from being strong.

This is [Siegel (Definition 5.17 on p. 218)][siegel:GeneralDeadendingUniverse:2025]
-/
@[expose] def NotErasable (A : AugmentedForm → Prop) (g : AugmentedForm) : Prop :=
  (¬ (g.hasTombstone .left ∧ Strong A (eraseLeftTomb g) .left)) ∧
    (¬ (g.hasTombstone .right ∧ Strong A (eraseRightTomb g) .right))

/--
This is [Siegel (Definition 5.19 on p. 219)][siegel:GeneralDeadendingUniverse:2025]
-/
def SimplestForm (A : AugmentedForm → Prop) (g : AugmentedForm) : Prop :=
  NoDominated A g ∧ NoReversible A g ∧ NotErasable A g ∧
    ∀ p, ∀ g' ∈ moves p g, SimplestForm A g'
  termination_by g
  decreasing_by form_wf

theorem simplestForm_iff {g : AugmentedForm} :
    SimplestForm U g ↔ NoDominated U g ∧ NoReversible U g ∧ NotErasable U g ∧
      ∀ p, ∀ g' ∈ moves p g, SimplestForm U g' := by
  rw [SimplestForm]

theorem SimplestForm.noDominated {g : AugmentedForm} (h : SimplestForm U g) :
    NoDominated U g := by rw [SimplestForm] at h; exact h.1

theorem SimplestForm.noReversible {g : AugmentedForm} (h : SimplestForm U g) :
    NoReversible U g := by rw [SimplestForm] at h; exact h.2.1

theorem SimplestForm.notErasable {g : AugmentedForm} (h : SimplestForm U g) :
    NotErasable U g := by rw [SimplestForm] at h; exact h.2.2.1

theorem SimplestForm.of_mem_moves {g g' : AugmentedForm} {p : Player}
    (h : SimplestForm U g) (hg' : g' ∈ moves p g) : SimplestForm U g' := by
  rw [SimplestForm] at h; exact h.2.2.2 p g' hg'

private theorem simplestForm_neg_mp [ClosedUnderNeg U] {g : AugmentedForm}
    (hg : SimplestForm U g) : SimplestForm U (-g) := by
  rw [simplestForm_iff]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨y, hy⟩
    exact (hg.noDominated).right
      ⟨-y, (dominatedRight_iff_neg (g := g) (gr := -y)).mpr (by simpa using hy)⟩
  · rintro ⟨y, hy⟩
    exact (hg.noDominated).left
      ⟨-y, by simpa using (dominatedRight_iff_neg (g := -g) (gr := y)).mp hy⟩
  · rintro ⟨gl, glr, h⟩
    exact (hg.noReversible).right
      ⟨-gl, -glr,
        (reversibleRight_iff_neg (g := g) (gr := -gl) (grl := -glr)).mpr (by simpa using h)⟩
  · rintro ⟨gr, grl, h⟩
    exact (hg.noReversible).left
      ⟨-gr, -grl, by simpa using (reversibleRight_iff_neg (g := -g) (gr := gr) (grl := grl)).mp h⟩
  · rintro ⟨ht, hs⟩
    refine (hg.notErasable).right ⟨by rwa [hasTombstone_neg_iff] at ht, ?_⟩
    have hee : eraseLeftTomb (-g) = -(eraseRightTomb g) := by
      rw [eraseRightTomb_eq_neg, neg_neg]
    rwa [hee, Strong.neg_iff (g := eraseRightTomb g), Player.neg_left] at hs
  · rintro ⟨ht, hs⟩
    refine (hg.notErasable).left ⟨by rwa [hasTombstone_neg_iff] at ht, ?_⟩
    have hee : eraseRightTomb (-g) = -(eraseLeftTomb g) := by
      rw [eraseRightTomb_eq_neg, neg_neg]
    rwa [hee, Strong.neg_iff (g := eraseLeftTomb g), Player.neg_right] at hs
  · intro p y hy
    have hy' : -y ∈ moves (-p) g := by rw [moves_neg, Set.mem_neg] at hy; exact hy
    have := simplestForm_neg_mp (hg.of_mem_moves hy')
    rwa [neg_neg] at this
termination_by g
decreasing_by form_wf

protected theorem SimplestForm.neg_iff [ClosedUnderNeg U] {g : AugmentedForm} :
    SimplestForm U g ↔ SimplestForm U (-g) :=
  ⟨simplestForm_neg_mp, fun h => by have := simplestForm_neg_mp h; rwa [neg_neg] at this⟩

-- TODO: Move
theorem misereEQ_of_forall_options [Hereditary U] {g h : AugmentedForm}
    (hLgh : ∀ gl ∈ moves .left g, ∃ hl ∈ moves .left h, gl =m U hl)
    (hLhg : ∀ hl ∈ moves .left h, ∃ gl ∈ moves .left g, gl =m U hl)
    (hRgh : ∀ gr ∈ moves .right g, ∃ hr ∈ moves .right h, gr =m U hr)
    (hRhg : ∀ hr ∈ moves .right h, ∃ gr ∈ moves .right g, gr =m U hr)
    (htomb : ∀ p, g.hasTombstone p ↔ h.hasTombstone p) :
    g =m U h := by
  apply MisereEq.of_antisymm
  · apply Hereditary.misereGE_of_maintenance_proviso
    · exact fun gr hgr => Or.inl <| by
        obtain ⟨hr, hhr, hgr⟩ := hRgh gr hgr
        exact ⟨hr, hhr, misereGE_of_misereEQ hgr⟩
    · intro hl hhl
      obtain ⟨gl, hgl, hgl'⟩ := hLhg hl hhl
      exact Or.inl ⟨gl, hgl, misereGE_of_misereEQ hgl'⟩
    · intro hend
      apply strong_of_isEndLike
      rw [IsEndLike_iff] at hend
      rw [IsEndLike_iff, ← htomb .right]
      rcases hend with ht | he
      · exact Or.inl ht
      · refine Or.inr ?_
        rw [isEnd_def, Set.eq_empty_iff_forall_notMem] at he ⊢
        intro hr hhr
        obtain ⟨gr, hgr, _⟩ := hRhg hr hhr
        exact he gr hgr
    · intro hend
      apply strong_of_isEndLike
      rw [IsEndLike_iff] at hend
      rw [IsEndLike_iff, htomb .left]
      rcases hend with ht | he
      · exact Or.inl ht
      · refine Or.inr ?_
        rw [isEnd_def] at he ⊢
        rw [Set.eq_empty_iff_forall_notMem] at he ⊢
        intro gl hgl
        obtain ⟨hl, hhl, _⟩ := hLgh gl hgl
        exact he hl hhl
  · apply Hereditary.misereGE_of_maintenance_proviso
    · intro gr hgr
      obtain ⟨gr', hgr', hgr''⟩ := hRhg gr hgr
      exact Or.inl ⟨gr', hgr', misereGE_of_misereEQ hgr''.symm⟩
    · intro gl hgl
      obtain ⟨hl, hhl, hgl⟩ := hLgh gl hgl
      exact Or.inl ⟨hl, hhl, by simpa [ hgl ] using misereGE_of_misereEQ hgl.symm⟩
    · intro hend
      apply strong_of_isEndLike
      rw [IsEndLike_iff] at hend
      rw [IsEndLike_iff, htomb .right]
      rcases hend with ht | he
      · exact Or.inl ht
      · refine Or.inr ?_
        rw [isEnd_def, Set.eq_empty_iff_forall_notMem] at he ⊢
        intro gr hgr
        obtain ⟨hr, hhr, _⟩ := hRgh gr hgr
        exact he hr hhr
    · intro hend
      apply strong_of_isEndLike
      rw [IsEndLike_iff] at hend
      rw [IsEndLike_iff, ← htomb .left]
      rcases hend with ht | he
      · exact Or.inl ht
      · refine Or.inr ?_
        rw [isEnd_def] at he ⊢
        rw [Set.eq_empty_iff_forall_notMem] at he ⊢
        intro hl hhl
        obtain ⟨gl, hgl, _⟩ := hLhg hl hhl
        exact he gl hgl

-- TODO: Siplt into three

/--
The Left irreducibility of a `treeSize`-minimal representative.
-/
private theorem noLeftReductions_of_minimal [ShortUniverse U] {g0 k : AugmentedForm}
    (h_k_shrot : IsShort k) (h_eq : k =m U g0)
    (h_moves_simplest : ∀ p, ∀ x ∈ moves p k, SimplestForm U x)
    (h_min : ∀ k', IsShort k' → (k' =m U g0) →
      (∀ p, ∀ x ∈ moves p k', SimplestForm U x) → treeSize k ≤ treeSize k') :
    (¬ ∃ gl, DominatedLeft U k gl) ∧
      (¬ ∃ gl glr, ReversibleLeftThrough U k gl glr) ∧
      ¬ (k.hasTombstone .left ∧ Strong U (eraseLeftTomb k) .left) := by
  refine' ⟨_, _, _⟩
  · rintro ⟨gl, h_gl_dom⟩
    refine not_lt_of_ge ?_ (treeSize_removeLeftOption_lt h_k_shrot h_gl_dom.left)
    have h_remove_moves_simpleset (p : Player) (x : AugmentedForm)
        (hx : x ∈ moves p (k.removeLeftOption gl)) : SimplestForm U x := by
      apply h_moves_simplest p x
      cases p
      · rw [leftMoves_removeLeftOption] at hx
        exact Set.mem_of_mem_inter_left hx
      · rwa [rightMoves_removeLeftOption] at hx
    exact h_min (removeLeftOption k gl) (isShort_removeLeftOption h_k_shrot gl)
      ((removeLeftOption_misereEQ h_gl_dom).trans h_eq) h_remove_moves_simpleset
  · rintro ⟨gl, glr, hgl, hglr, h⟩
    by_cases hend : IsEnd .left glr
    · have hK'_misereEQ : atomicReplaceLeft k gl =m U k := by
        apply atomicReplaceLeft_misereEQ h_k_shrot ⟨hgl, hglr, h⟩ hend
      have h_replace_moves_simplest (p : Player) (x : AugmentedForm)
          (hx : x ∈ moves p (atomicReplaceLeft k gl)) : SimplestForm U x := by
        apply h_moves_simplest p x
        cases p
        · rw [leftMoves_atomicReplaceLeft] at hx
          exact Set.mem_of_mem_inter_left hx
        · rwa [rightMoves_atomicReplaceLeft] at hx
      absurd (h_min (atomicReplaceLeft k gl) (isShort_atomicReplaceLeft h_k_shrot)
          (hK'_misereEQ.trans h_eq) h_replace_moves_simplest)
      exact not_le.mpr (treeSize_atomicReplaceLeft_lt h_k_shrot hgl hglr)
    · have hK'_short : IsShort (openBypassLeft k gl glr) :=
        isShort_openBypassLeft h_k_shrot
          (Short.of_mem_moves (Short.of_mem_moves h_k_shrot hgl) hglr)
      have hK'_eq : openBypassLeft k gl glr =m U g0 := by
        have hK'_eq : openBypassLeft k gl glr =m U k := by
          apply AugmentedForm.openBypassLeft_misereEQ h_k_shrot ⟨hgl, hglr, h⟩ hend
        exact MisereEQ.trans hK'_eq h_eq
      have h_bypass_moves_simplest (p : Player) (x : AugmentedForm)
          (hx : x ∈ moves p (openBypassLeft k gl glr)) : SimplestForm U x := by
        have hx_cases : x ∈ moves p k ∨ x ∈ moves p glr := by
          cases p
          · rw [leftMoves_openBypassLeft] at hx
            rcases hx with hxK | hxglr
            · exact Or.inl hxK.left
            · exact Or.inr hxglr
          · rw [rightMoves_openBypassLeft] at hx
            exact Or.inl hx
        rcases hx_cases with hxK | hxglr
        · exact h_moves_simplest p x hxK
        · exact SimplestForm.of_mem_moves ((h_moves_simplest .left gl hgl).of_mem_moves hglr) hxglr
      exact not_lt_of_ge (h_min _ hK'_short hK'_eq h_bypass_moves_simplest)
        (treeSize_openBypassLeft_lt h_k_shrot hgl hglr)
  · intro h_contra
    obtain ⟨htomb, hstrong⟩ := h_contra
    have hK'_eq : (AugmentedForm.eraseLeftTomb k) =m U k := by
      exact eraseLeftTomb_misereEQ h_k_shrot htomb hstrong
    have hK'_opt : ∀ p, ∀ x ∈ moves p (AugmentedForm.eraseLeftTomb k), SimplestForm U x := by
      exact fun p x hx => h_moves_simplest p x <| by simpa [ AugmentedForm.moves_eraseLeftTomb ] using hx
    have hK'_treeSize :
        (AugmentedForm.treeSize (AugmentedForm.eraseLeftTomb k)) < (AugmentedForm.treeSize k) := by
      exact treeSize_eraseLeftTomb_lt h_k_shrot htomb
    exact not_lt_of_ge
      (h_min _ (AugmentedForm.isShort_eraseLeftTomb h_k_shrot) (hK'_eq.trans h_eq) hK'_opt) hK'_treeSize

/--
A `treeSize`-minimal representative (among $\mathcal{U}$-equivalents whose
options are in simplest form) is itself in $\mathcal{U}$-simplest form.
-/
private theorem simplestForm_of_minimal [ShortUniverse U] {g0 k : AugmentedForm}
    (h_short : IsShort k) (h_eq : k =m U g0)
    (h_moves_simplest : ∀ p, ∀ x ∈ moves p k, SimplestForm U x)
    (h_min : ∀ k', IsShort k' → (k' =m U g0) →
      (∀ p, ∀ x ∈ moves p k', SimplestForm U x) → treeSize k ≤ treeSize k') :
    SimplestForm U k := by
  rw [SimplestForm.neg_iff]
  apply Classical.byContradiction
  intro h_contra
  obtain ⟨hND_left, hNR_left, hNE_left⟩ := noLeftReductions_of_minimal h_short h_eq h_moves_simplest h_min
  have hKopt_neg : ∀ p, ∀ x ∈ moves p (-k), SimplestForm U x := by
    intro p x h_x_mem
    simp only [moves_neg, Set.mem_neg] at h_x_mem
    have := h_moves_simplest (-p) (-x) h_x_mem
    rwa [SimplestForm.neg_iff]
  have hmin_neg : ∀ (k' : AugmentedForm), IsShort k' → k' =m U-g0 →
      (∀ (p : Player), ∀ x ∈ moves p k', SimplestForm U x) → (-k).treeSize ≤ k'.treeSize := by
    intros K' hK' hKeq' hKopt'
    convert h_min (-K') (Short.neg hK') (by simpa using misereEQ_neg_iff.mpr hKeq') (by
      intro p x hx
      rw [moves_neg] at hx
      have := (hKopt' (-p) (-x) hx)
      rwa [SimplestForm.neg_iff]) using 1
    · exact treeSize_neg
    · rw [AugmentedForm.treeSize_neg]
  obtain ⟨hND_right, hNR_right, hNE_right⟩ :=
    noLeftReductions_of_minimal (Short.neg h_short) (misereEQ_neg_iff.mpr h_eq) hKopt_neg hmin_neg
  refine h_contra ?_
  rw [simplestForm_iff]
  refine ⟨⟨hND_right, ?_⟩, ⟨hNR_right, ?_⟩, ⟨hNE_right, ?_⟩, fun p x hx => ?_⟩
  · rintro ⟨gr, hgr⟩
    exact hND_left ⟨-gr, by simpa using dominatedRight_iff_neg.mp hgr⟩
  · rintro ⟨gr, grl, hh⟩
    exact hNR_left ⟨-gr, -grl, by simpa using reversibleRight_iff_neg.mp hh⟩
  · convert hNE_left using 1
    rw [hasTombstone_neg_iff, eraseRightTomb_eq_neg, Strong.neg_iff]
    simp [Player.neg_right]
  · rw [moves_neg] at hx
    have := (h_moves_simplest (-p) (-x) hx)
    rwa [SimplestForm.neg_iff]

private theorem exists_simplestForm_step [ShortUniverse U] {g : AugmentedForm} (hg : IsShort g)
    (IH : ∀ p, ∀ o ∈ moves p g, ∃ k : AugmentedForm,
      IsShort k ∧ SimplestForm U k ∧ (k =m U o)) :
    ∃ k : AugmentedForm, IsShort k ∧ SimplestForm U k ∧ (k =m U g) := by
  obtain ⟨SF, hShort, hSimp, hEq⟩ :
      ∃ SF : Player → AugmentedForm → AugmentedForm,
        (∀ p o, o ∈ moves p g → IsShort (SF p o)) ∧
          (∀ p o, o ∈ moves p g → SimplestForm U (SF p o)) ∧
            (∀ p o, o ∈ moves p g → (SF p o =m U o)) := by
    choose! SF hSF₁ hSF₂ hSF₃ using IH; exact ⟨_, hSF₁, hSF₂, hSF₃⟩
  -- Define `g0` as the form with options `SF p o` for `o ∈ moves p g` and the
  -- same tombstones as `g`.
  set g0 := AugmentedForm.ofSetsWithTombs (fun p => (fun o => SF p o) '' moves p g)
    (fun p => g.hasTombstone p) with hg0_def
  have hg0_short : IsShort g0 := by
    apply Short.mk
    intro p
    simp [hg0_def, moves_ofSetsWithTombs]
    exact ⟨Set.Finite.image _ (Short.finite_moves p hg), fun a ha => hShort p a ha⟩
  have hg0_eq : g0 =m U g := by
    apply misereEQ_of_forall_options
    · simp [hg0_def] at ⊢ hEq
      exact fun o ho => ⟨o, ho, hEq.1 o ho⟩
    · intro hl hhl
      use SF Player.left hl
      constructor
      · rw [moves_ofSetsWithTombs]; exact Set.mem_image_of_mem _ hhl
      · exact hEq Player.left hl hhl
    · intro gr hgr
      rw [AugmentedForm.moves_ofSetsWithTombs] at hgr
      obtain ⟨o, ho, rfl⟩ := hgr
      exact ⟨o, ho, hEq .right o ho⟩
    · intro hr hhr
      refine ⟨SF .right hr, ?_, hEq .right hr hhr⟩
      rw [moves_ofSetsWithTombs]
      exact Set.mem_image_of_mem _ hhr
    · simp [g0, AugmentedForm.hasTombstone_ofSetsWithTombs]
  have hg0_opt : ∀ p, ∀ x ∈ moves p g0, SimplestForm U x := by
    intro p x hx
    rw [AugmentedForm.moves_ofSetsWithTombs] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    exact hSimp p o ho
  -- Minimize the tree size of `g0` to obtain a simplest form `K`.
  obtain ⟨K, hK⟩ : ∃ K, IsShort K ∧ (K =m U g0) ∧
      (∀ p, ∀ x ∈ moves p K, SimplestForm U x) ∧ ∀ K', IsShort K' → (K' =m U g0) →
        (∀ p, ∀ x ∈ moves p K', SimplestForm U x) → treeSize K ≤ treeSize K' := by
    have hP : ∃ n, ∃ K, IsShort K ∧ K =m U g0 ∧
        (∀ p, ∀ x ∈ moves p K, SimplestForm U x) ∧ treeSize K = n := by
      exact ⟨_, _, hg0_short, (fun x _ => rfl) , hg0_opt, rfl⟩
    obtain ⟨n, K, hK_short, hK_eq, hK_opt, hK_min⟩ := hP
    have h_min : ∃ m ∈ {n | ∃ K, IsShort K ∧ K =m U g0 ∧
        (∀ p, ∀ x ∈ moves p K, SimplestForm U x) ∧ treeSize K = n},
        ∀ n ∈ {n | ∃ K, IsShort K ∧ K =m U g0 ∧
          (∀ p, ∀ x ∈ moves p K, SimplestForm U x) ∧ treeSize K = n}, m ≤ n := by
        simpa using wellFounded_lt.has_min
          { n | ∃ K, IsShort K ∧ K =m U g0 ∧
            (∀ p, ∀ x ∈ moves p K, SimplestForm U x) ∧ K.treeSize = n }
          ⟨_, ⟨K, hK_short, hK_eq, hK_opt, hK_min⟩⟩
    obtain ⟨m, ⟨K, hK_short, hK_eq, hK_opt, rfl⟩, hm⟩ := h_min
    exact ⟨K, hK_short, hK_eq, hK_opt,
      fun K' hK'_short hK'_eq hK'_opt => hm _ ⟨K', hK'_short, hK'_eq, hK'_opt, rfl⟩⟩
  exact ⟨K, hK.1, simplestForm_of_minimal hK.1 hK.2.1 hK.2.2.1 hK.2.2.2, hK.2.1.trans hg0_eq⟩

theorem exists_simplestForm [ShortUniverse U] {g : AugmentedForm} (hg : IsShort g) :
    ∃ k : AugmentedForm, IsShort k ∧ SimplestForm U k ∧ (k =m U g) :=
  exists_simplestForm_step hg
    (fun p o ho => exists_simplestForm (Short.of_mem_moves hg ho))
termination_by g
decreasing_by form_wf

private theorem simplestForm_ge_right [ShortUniverse U] {g h : AugmentedForm}
    (h_g_short : IsShort g) (h_h_short : IsShort h)
    (h_g_simplest : SimplestForm U g) (h_eq : g =m U h) :
    ∀ gr ∈ moves .right g, ∃ hr ∈ moves .right h, gr ≥m U hr := by
  obtain ⟨M₁, M₂, P₁, P₂⟩ := Form.ComparisonSet.maintenance_proviso_of_misereGE
    h_g_short h_h_short (misereGE_of_misereEQ h_eq);
  intro gr hgr
  specialize M₁ gr hgr
  rcases M₁ with (⟨hr, hhr, hge⟩ | ⟨grl, hgrl, hge⟩) ;
  · use hr, hhr, hge
  · absurd h_g_simplest.noReversible.right
    use gr, grl, hgr, hgrl, misereGE_rw_right h_eq hge

private theorem simplestForm_eq_right [ShortUniverse U] {g h : AugmentedForm}
    (h_g_short : IsShort g) (h_h_short : IsShort h)
    (h_g_simplest : SimplestForm U g) (h_h_simplest : SimplestForm U h)
    (h_eq : g =m U h) :
    ∀ gr ∈ moves .right g, ∃ hr ∈ moves .right h, gr =m U hr := by
  intro gr h_gr_mem
  have ⟨hr, hhr, hge1⟩ := simplestForm_ge_right h_g_short h_h_short h_g_simplest h_eq gr h_gr_mem
  have ⟨gr', hgr', hge2⟩ := simplestForm_ge_right h_h_short h_g_short h_h_simplest h_eq.symm hr hhr
  by_cases h_eq_gr : gr = gr'
  · exact ⟨hr, hhr, MisereEq.of_antisymm hge1 (h_eq_gr ▸ hge2)⟩
  · absurd h_g_simplest.noDominated.right
    use gr, h_gr_mem, gr', hgr', Ne.symm h_eq_gr, MisereGE.trans hge1 hge2

private theorem simplestForm_ge_left [ShortUniverse U] {g h : AugmentedForm}
    (h_g_short : IsShort g) (h_h_short : IsShort h)
    (h_g_simplest : SimplestForm U g) (h_eq : g =m U h) :
    ∀ gl ∈ moves .left g, ∃ hl ∈ moves .left h, hl ≥m U gl := by
  obtain ⟨M, P⟩ := Form.ComparisonSet.maintenance_proviso_of_misereGE
      h_h_short h_g_short (misereGE_of_misereEQ h_eq.symm)
  simp only [Maintenance] at M P
  intro gl h_gl_mem
  specialize P
  rcases P.left gl h_gl_mem with (⟨hl, hhl, hge⟩ | ⟨hlr, hhlr, hge⟩)
  · use hl, hhl, hge
  · absurd h_g_simplest.noReversible.left
    use gl, hlr, h_gl_mem, hhlr, misereGE_rw_left h_eq.symm hge

private theorem simplestForm_eq_left [ShortUniverse U] {g h : AugmentedForm}
    (h_g_short : IsShort g) (h_h_short : IsShort h)
    (h_g_simplest : SimplestForm U g) (h_h_simplest : SimplestForm U h)
    (h_eq : g =m U h) :
    ∀ gl ∈ moves .left g, ∃ hl ∈ moves .left h, gl =m U hl := by
  intro gl hgl
  obtain ⟨hl, hhl, hge1⟩ := simplestForm_ge_left h_g_short h_h_short h_g_simplest h_eq gl hgl
  obtain ⟨gl', hgl', hge2⟩ := simplestForm_ge_left h_h_short h_g_short h_h_simplest h_eq.symm hl hhl
  by_cases hEq : gl = gl';
  · exact ⟨hl, hhl, MisereEq.of_antisymm (by simpa [ hEq ] using hge2) hge1⟩;
  · exact False.elim <| h_g_simplest.noDominated.1 ⟨gl, hgl, gl', hgl', Ne.symm hEq, MisereGE.trans hge2 hge1⟩

theorem strong_of_hasTombstone {p : Player} {g : AugmentedForm}
    (h : g.hasTombstone p) : Strong U g p :=
  strong_of_isEndLike (Or.inl h)

mutual

theorem winsGoingFirst_left_eraseRightTomb (g h : AugmentedForm)
    (h_win : WinsGoingFirst .left (g + h)) :
    WinsGoingFirst .left (eraseRightTomb g + h) := by
  have h_end_L : IsEndLike .left (eraseRightTomb g) ↔ IsEndLike .left g := by
    simp [IsEndLike_iff, hasTombstone_left_eraseRightTomb, isEnd_def, moves_eraseRightTomb]
  rw [winsGoingFirst_iff] at h_win
  rcases h_win with h_end | ⟨z, h_z_mem, h_z_win⟩
  · apply winsGoingFirst_of_isEndLike
    rw [IsEndLike.add_iff] at h_end ⊢
    exact ⟨h_end_L.mpr h_end.left, h_end.right⟩
  · rw [moves_add, Set.mem_union, Set.mem_image, Set.mem_image] at h_z_mem
    rcases h_z_mem with ⟨gl, hgl, rfl⟩ | ⟨yl, hyl, rfl⟩
    · refine winsGoingFirst_of_moves ⟨gl + h, ?_, h_z_win⟩
      exact add_right_mem_moves_add (by rwa [moves_eraseRightTomb]) h
    · refine winsGoingFirst_of_moves ⟨eraseRightTomb g + yl, add_left_mem_moves_add hyl _, ?_⟩
      intro h
      exact h_z_win (winsGoingFirst_right_eraseRightTomb g yl h)
termination_by h
decreasing_by form_wf

theorem winsGoingFirst_right_eraseRightTomb (g h : AugmentedForm)
    (h_win : WinsGoingFirst .right (eraseRightTomb g + h)) :
    WinsGoingFirst .right (g + h) := by
  have h_end_R : IsEndLike .right (eraseRightTomb g) → IsEndLike .right g := by
    intro h
    rw [IsEndLike_iff] at h ⊢
    rcases h with h | h
    · exact absurd h (hasTombstone_right_eraseRightTomb g)
    · exact Or.inr (by simpa [isEnd_def, moves_eraseRightTomb] using h)
  rw [winsGoingFirst_iff] at h_win
  rcases h_win with h_end | ⟨z, h_z_mem, h_z_win⟩
  · apply winsGoingFirst_of_isEndLike
    rw [IsEndLike.add_iff] at h_end ⊢
    exact ⟨h_end_R h_end.left, h_end.right⟩
  · rw [moves_add, Set.mem_union, Set.mem_image, Set.mem_image] at h_z_mem
    rcases h_z_mem with ⟨gr, hgr, rfl⟩ | ⟨yr, hyr, rfl⟩
    · refine winsGoingFirst_of_moves ⟨gr + h, ?_, h_z_win⟩
      exact add_right_mem_moves_add (by rwa [moves_eraseRightTomb] at hgr) h
    · refine winsGoingFirst_of_moves ⟨g + yr, add_left_mem_moves_add hyr _, ?_⟩
      exact fun h => h_z_win (winsGoingFirst_left_eraseRightTomb g yr h)
termination_by h
decreasing_by form_wf

end

theorem strong_left_eraseRightTomb {g : AugmentedForm} (h : Strong U g .left) :
    Strong U (eraseRightTomb g) .left := by
  intro x hx h_end
  exact winsGoingFirst_left_eraseRightTomb g x (h x hx h_end)

theorem eraseRightTomb_misereEQ [Hereditary U] {g : AugmentedForm}
    (h_strong : Strong U (eraseRightTomb g) .right) :
    (eraseRightTomb g) =m U g := by
  apply MisereEq.of_antisymm
  · apply Hereditary.misereGE_of_maintenance_proviso
    · intro gr h_gr_mem
      exact Or.inl ⟨gr, by simpa [moves_eraseRightTomb] using h_gr_mem, MisereGE.refl _⟩
    · intro hl h_hl_mem
      exact Or.inl ⟨hl, by simpa [moves_eraseRightTomb] using h_hl_mem, MisereGE.refl _⟩
    · intro h_end
      apply strong_of_isEndLike
      simpa [IsEndLike_iff, isEnd_def] using Or.inr h_end
    · intro h_end
      apply strong_of_isEndLike
      simpa [IsEndLike_iff, hasTombstone_left_eraseRightTomb, isEnd_def] using h_end
  · apply Hereditary.misereGE_of_maintenance_proviso
    · intro gr hgr
      exact Or.inl ⟨gr, by simpa [moves_eraseRightTomb] using hgr, MisereGE.refl _⟩
    · intro hl h_hl_mem
      exact Or.inl ⟨hl, by simpa [moves_eraseRightTomb] using h_hl_mem, MisereGE.refl _⟩
    · intro h_end
      exact h_strong
    · intro h_end
      apply strong_of_isEndLike
      simpa [IsEndLike_iff, hasTombstone_left_eraseRightTomb, isEnd_def] using h_end

-- TODO: Move
private theorem strong_congr_misereEQ {g h : AugmentedForm} {p : Player}
    (h_eq : g =m U h) : Strong U g p ↔ Strong U h p := by
  have aux : ∀ {a b : AugmentedForm}, a =m U b → Strong U a p → Strong U b p :=
    fun h_eq h_strong x hx h_x_end =>
      (misereOutcome_eq_winsGoingFirst_iff (h_eq x hx)).mp (h_strong x hx h_x_end)
  exact ⟨aux h_eq, aux h_eq.symm⟩

private theorem simplestForm_tomb_eq_left [ShortUniverse U] {g h : AugmentedForm}
    (h_g_simplest : SimplestForm U g) (h_eq : g =m U h)
    (h_moves_eq : ∀ p, moves p g = moves p h) (h_g_tomb_L : hasTombstone .left g) :
    hasTombstone .left h := by
    by_contra h_h_tomb_L
    have h_g_strong : Strong U g .left := strong_of_hasTombstone h_g_tomb_L
    have h_h_strong : Strong U h .left := (strong_congr_misereEQ h_eq).mp h_g_strong
    have h_erase_not_strong : ¬ Strong U (eraseLeftTomb g) .left :=
      fun hs => (h_g_simplest.notErasable).left ⟨h_g_tomb_L, hs⟩
    by_cases h_g_tomb_R : hasTombstone .right g
    · by_cases h_h_tomb_R : hasTombstone .right h
      · have h_erase_eq : eraseLeftTomb g = h := by
          ext p
          · simp [h_moves_eq]
          · cases p
            · simp [hasTombstone_left_eraseLeftTomb, h_h_tomb_L]
            · simp [hasTombstone_right_eraseLeftTomb, h_g_tomb_R, h_h_tomb_R]
        absurd h_erase_not_strong
        rwa [h_erase_eq]
      · have h_erase_eq : eraseRightTomb (eraseLeftTomb g) = h := by
          ext p
          · rw [moves_eraseRightTomb, moves_eraseLeftTomb, h_moves_eq p]
          · cases p
            · simp [h_h_tomb_L, hasTombstone_left_eraseRightTomb, hasTombstone_left_eraseLeftTomb]
            · simp [h_h_tomb_R, hasTombstone_right_eraseRightTomb]
        have h_g_strong_R : Strong U g .right := strong_of_hasTombstone h_g_tomb_R
        have h_h_string_R : Strong U h .right := (strong_congr_misereEQ h_eq).1 h_g_strong_R
        have h_erase_strong_R : Strong U (eraseRightTomb (eraseLeftTomb g)) .right := by
          rwa [h_erase_eq]
        have h_erase_eq_erase : eraseRightTomb (eraseLeftTomb g) =m U eraseLeftTomb g :=
          eraseRightTomb_misereEQ h_erase_strong_R
        have h_erase_eq : eraseLeftTomb g =m U g :=
          ((h_erase_eq ▸ h_erase_eq_erase).symm).trans h_eq.symm
        exact h_erase_not_strong ((strong_congr_misereEQ h_erase_eq).2 h_g_strong)
    · by_cases h_h_tomb_R : h.hasTombstone .right
      · have h_erase_eq_erase : eraseLeftTomb g = eraseRightTomb h := by
          ext p
          · rw [moves_eraseLeftTomb, moves_eraseRightTomb, h_moves_eq p]
          · cases p
            · simp [hasTombstone_left_eraseLeftTomb, hasTombstone_left_eraseRightTomb, h_h_tomb_L]
            · simp [hasTombstone_right_eraseLeftTomb, hasTombstone_right_eraseRightTomb, h_g_tomb_R]
        have h_erase_strong : Strong U (eraseRightTomb h) .left := strong_left_eraseRightTomb h_h_strong
        absurd h_erase_not_strong
        rwa [h_erase_eq_erase]
      · have h_erase_eq : eraseLeftTomb g = h := by
          ext p
          · rw [moves_eraseLeftTomb, h_moves_eq p]
          · cases p
            · simp [hasTombstone_left_eraseLeftTomb, h_h_tomb_L]
            · simp [hasTombstone_right_eraseLeftTomb, h_g_tomb_R, h_h_tomb_R]
        absurd h_erase_not_strong
        rwa [h_erase_eq]

private theorem simplestForm_tomb_eq [ShortUniverse U] {p : Player} {g h : AugmentedForm}
    (h_g_simplest : SimplestForm U g) (h_h_simplest : SimplestForm U h)
    (h_eq : g =m U h) (h_moves_eq : ∀ p, moves p g = moves p h) :
    g.hasTombstone p ↔ h.hasTombstone p := by
  cases p with
  | left =>
    exact ⟨simplestForm_tomb_eq_left h_g_simplest h_eq h_moves_eq,
           simplestForm_tomb_eq_left h_h_simplest h_eq.symm (fun p => (h_moves_eq p).symm)⟩
  | right =>
    have h_g_neg_simplest : SimplestForm U (-g) := SimplestForm.neg_iff.mp h_g_simplest
    have h_h_neg_simplest : SimplestForm U (-h) := SimplestForm.neg_iff.mp h_h_simplest
    have h_neg_eq : (-g) =m U (-h) := misereEQ_neg_iff.mpr h_eq
    have h_neg_moves_eq (p : Player) : moves p (-g) = moves p (-h) := by
      rw [moves_neg, moves_neg, h_moves_eq (-p)]
    constructor
    · intro hgR
      have hgt : (-g).hasTombstone .left := by rwa [hasTombstone_neg_iff]
      have := simplestForm_tomb_eq_left h_g_neg_simplest h_neg_eq h_neg_moves_eq hgt
      rwa [hasTombstone_neg_iff] at this
    · intro hhR
      have hht : (-h).hasTombstone .left := by rwa [hasTombstone_neg_iff]
      have h_neg_moves_eq_symm (p : Player) := (h_neg_moves_eq p).symm
      have := simplestForm_tomb_eq_left h_h_neg_simplest h_neg_eq.symm h_neg_moves_eq_symm hht
      rwa [hasTombstone_neg_iff] at this

/--
This is [Siegel (Theorem 5.18 on p. 218)][siegel:GeneralDeadendingUniverse:2025]
-/
theorem simplestForm_unique [ShortUniverse U] {g h : AugmentedForm}
    (h_g_short : IsShort g) (h_g_simplest : SimplestForm U g)
    (h_h_short : IsShort h) (h_h_simplest : SimplestForm U h)
    (heq : g =m U h) :
    g = h := by
  have h_moves_eq (p : Player) : moves p g = moves p h := by
    apply Set.eq_of_subset_of_subset
    · intro g' h_g'_mem
      obtain ⟨h', h_h'_mem, h_h'_eq⟩ : ∃ ho ∈ moves p h, g' =m U ho := by
        cases p
        · exact simplestForm_eq_left h_g_short h_h_short h_g_simplest h_h_simplest heq g' h_g'_mem
        · exact simplestForm_eq_right h_g_short h_h_short h_g_simplest h_h_simplest heq g' h_g'_mem
      have h_h'_identical : g' = h' :=
        simplestForm_unique (Short.of_mem_moves h_g_short h_g'_mem) (h_g_simplest.of_mem_moves h_g'_mem)
          (Short.of_mem_moves h_h_short h_h'_mem) (h_h_simplest.of_mem_moves h_h'_mem) h_h'_eq
      rwa [h_h'_identical]
    · intro h' h_h'_mem
      obtain ⟨g', h_g'_mem, h_g'_eq⟩ : ∃ go ∈ moves p g, h' =m U go := by
        cases p
        · exact simplestForm_eq_left h_h_short h_g_short h_h_simplest h_g_simplest heq.symm h' h_h'_mem
        · exact simplestForm_eq_right h_h_short h_g_short h_h_simplest h_g_simplest heq.symm h' h_h'_mem
      have h_g'_identical : g' = h' :=
        simplestForm_unique (Short.of_mem_moves h_g_short h_g'_mem) (h_g_simplest.of_mem_moves h_g'_mem)
          (Short.of_mem_moves h_h_short h_h'_mem) (h_h_simplest.of_mem_moves h_h'_mem) h_g'_eq.symm
      rwa [←h_g'_identical]
  refine AugmentedForm.ext h_moves_eq ?_
  intro p
  exact simplestForm_tomb_eq h_g_simplest h_h_simplest heq h_moves_eq
termination_by g
decreasing_by form_wf

end AugmentedForm
