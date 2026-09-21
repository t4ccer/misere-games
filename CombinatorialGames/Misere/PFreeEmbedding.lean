/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.PFreeBlocking
public import CombinatorialGames.Misere.PFreeBlockingEnds
public import CombinatorialGames.Misere.PFreeDeadEnding

/-!
# $\operatorname{pf}(\mathcal{E})$ embeds in $\operatorname{pf}(\mathcal{B})$

Every short dead-ending form is short blocking, and on forms of
$\operatorname{pf}(\mathcal{E})$ comparison modulo $\operatorname{pf}(\mathcal{E})$ and modulo
$\operatorname{pf}(\mathcal{B})$ agree (`misereGE_pfree_iff_of_subset`), so the quotient of
$\operatorname{pf}(\mathcal{E})$ embeds in the quotient of $\operatorname{pf}(\mathcal{B})$ as an
ordered monoid. Since every end of $\operatorname{pf}(\mathcal{B})$ is an integer
(`PFreeBlocking.isEnd_exists_intCast_misereEQ`), the embedding is onto
(`exists_pfreeDeadEnding_misereEQ`), so the two quotients are isomorphic.

The main results are
* `misereGE_pfreeDeadEnding_iff_pfreeBlocking`
* `misereEQ_pfreeDeadEnding_iff_pfreeBlocking`
* `exists_pfreeDeadEnding_misereEQ`
-/

public section

universe u

open Form
open Form.Misere.Outcome
open GameForm
open PFree

namespace PFree

theorem shortBlocking_of_shortDeadEnding {g : GameForm} (h_g : DeadEnding.ShortDeadEnding g) :
    ShortBlocking g :=
  ⟨h_g.short, isBlocking_of_isDeadEnding h_g.dead_ending⟩

theorem pfreeBlocking_of_pfreeDeadEnding {g : GameForm} (h_g : PFreeDeadEnding g) :
    PFreeBlocking g :=
  pfreeSubset_of_subset (U := ShortBlocking) (fun _ => shortBlocking_of_shortDeadEnding) h_g

theorem misereGE_pfreeDeadEnding_iff_pfreeBlocking {g h : GameForm}
    (h_g : PFreeDeadEnding g) (h_h : PFreeDeadEnding h) :
    g ≥m PFreeDeadEnding h ↔ g ≥m PFreeBlocking h :=
  misereGE_pfree_iff_of_subset (U := ShortBlocking) (V := DeadEnding.ShortDeadEnding)
    (fun _ => shortBlocking_of_shortDeadEnding) h_g h_h

theorem misereEQ_pfreeDeadEnding_iff_pfreeBlocking {g h : GameForm}
    (h_g : PFreeDeadEnding g) (h_h : PFreeDeadEnding h) :
    g =m PFreeDeadEnding h ↔ g =m PFreeBlocking h :=
  misereEQ_pfree_iff_of_subset (U := ShortBlocking) (V := DeadEnding.ShortDeadEnding)
    (fun _ => shortBlocking_of_shortDeadEnding) h_g h_h

/--
Every form of $\operatorname{pf}(\mathcal{B})$ is equivalent modulo
$\operatorname{pf}(\mathcal{B})$ to a form of $\operatorname{pf}(\mathcal{E})$: ends are
integers, and in a non-end every option can be replaced by an equivalent dead-ending form.
-/
theorem exists_pfreeDeadEnding_misereEQ {g : GameForm} (h_g : PFreeBlocking g) :
    ∃ h : GameForm, PFreeDeadEnding h ∧ g =m PFreeBlocking h := by
  by_cases h_end : ∃ p, IsEnd p g
  · obtain ⟨p, h_end⟩ := h_end
    obtain ⟨k, h_k⟩ := PFreeBlocking.isEnd_exists_intCast_misereEQ h_g h_end
    exact ⟨((k : ℤ) : GameForm), HasInt.has_int k, h_k⟩
  · push_neg at h_end
    have h_opt : ∀ p, ∀ gp ∈ moves p g,
        ∃ hp : GameForm, PFreeDeadEnding hp ∧ gp =m PFreeBlocking hp :=
      fun p gp h_gp => exists_pfreeDeadEnding_misereEQ (Hereditary.of_mem_moves h_g h_gp)
    choose! rep h_rep using h_opt
    have h_short := Short.isShort h_g
    have h_eq :
        g =m PFreeBlocking !{rep .left '' moves .left g | rep .right '' moves .right g} := by
      refine Hereditary.misereEQ_of_moves ?_ ?_ ?_ ?_
      · intro gl h_gl
        refine ⟨rep .left gl, ?_, (h_rep .left gl h_gl).right⟩
        rw [leftMoves_ofSets]
        exact Set.mem_image_of_mem _ h_gl
      · intro hl h_hl
        rw [leftMoves_ofSets] at h_hl
        obtain ⟨gl, h_gl, rfl⟩ := h_hl
        exact ⟨gl, h_gl, (h_rep .left gl h_gl).right.symm⟩
      · intro gr h_gr
        refine ⟨rep .right gr, ?_, (h_rep .right gr h_gr).right⟩
        rw [rightMoves_ofSets]
        exact Set.mem_image_of_mem _ h_gr
      · intro hr h_hr
        rw [rightMoves_ofSets] at h_hr
        obtain ⟨gr, h_gr, rfl⟩ := h_hr
        exact ⟨gr, h_gr, (h_rep .right gr h_gr).right.symm⟩
    have h_moves : ∀ p, ∀ hp ∈ moves p !{rep .left '' moves .left g | rep .right '' moves .right g},
        PFreeDeadEnding hp := by
      intro p hp h_hp
      cases p
      · rw [leftMoves_ofSets] at h_hp
        obtain ⟨gl, h_gl, rfl⟩ := h_hp
        exact (h_rep .left gl h_gl).left
      · rw [rightMoves_ofSets] at h_hp
        obtain ⟨gr, h_gr, rfl⟩ := h_hp
        exact (h_rep .right gr h_gr).left
    refine ⟨_, PFreeSubset.mk ⟨?_, ?_⟩ ?_, h_eq⟩
    · refine IsShort.ofSets ((IsShort.finite_moves _ h_short).image _) ?_
        ((IsShort.finite_moves _ h_short).image _) ?_
      · intro hl h_hl
        exact (h_moves .left hl (by rwa [leftMoves_ofSets])).mem.short
      · intro hr h_hr
        exact (h_moves .right hr (by rwa [rightMoves_ofSets])).mem.short
    · unfold IsDeadEnding
      refine ⟨?_, ?_⟩
      · intro p h_p
        exfalso
        refine h_end p ?_
        rw [isEnd_def] at h_p ⊢
        cases p
        · rw [leftMoves_ofSets] at h_p
          exact Set.image_eq_empty.mp h_p
        · rw [rightMoves_ofSets] at h_p
          exact Set.image_eq_empty.mp h_p
      · intro p hp h_hp
        exact (h_moves p hp h_hp).mem.dead_ending
    · unfold IsPFree
      refine ⟨?_, ?_⟩
      · rw [← IntegerInvertible.misereOutcome_eq_of_misereEQ h_eq]
        exact misereOutcome_ne_P_of_pfree h_g
      · intro p hp h_hp
        exact (h_moves p hp h_hp).isPFree
termination_by g
decreasing_by form_wf

end PFree
