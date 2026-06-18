/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import CombinatorialGames.Form.Short

universe u

public section

namespace Form

open Classical in
/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
This extends the notion of the
_adjoint_ of a short augmented form, as defined by
[Siegel (Definition 5.6 on p. 214)][siegel:GeneralDeadendingUniverse:2025], to
transfinite forms:
$$
G^\circ =
\begin{cases}
*
& \text{if } G \text{ has no ordinary options},\\
\form<\left(G^\mathcal{R}\right)^\circ>[0]
& \text{if} G \text{ has ordinary Right options, but no ordinary Left options},\\
\form<0>[\left(G^\mathcal{L}\right)^\circ]
& \text{if} G \text{ has ordinary Left options, but no ordinary Right options},\\
\form<\left(G^\mathcal{R}\right)^\circ>[\left(G^\mathcal{L}\right)^\circ]
& \text{otherwise}.
\end{cases}
$$

[Siegel (Definition 3.2 on p. 228)][siegel:CanonicalPartizan:2015] originally
defined this just for short game forms, which was a partizan analogue to the
impartial _mate_ due to [Conway (p. 147)][conway:NumbersAndGames:2001].

-/
@[expose] noncomputable def adjoint {G : Type (u + 1)} [Form G] (g : G) : G :=
  have := moves_small.{u} .left g
  have := moves_small.{u} .right g
  if IsEnd .left g ∧ IsEnd .right g then !{{0} | {0}}
  else if IsEnd .left g then !{Set.range fun gr : moves .right g => adjoint (gr : G) | {0}}
  else if IsEnd .right g then !{{0} | Set.range fun gl : moves .left g => adjoint (gl : G)}
  else !{ Set.range fun gr : moves .right g => adjoint (gr : G)
        | Set.range fun gl : moves .left g => adjoint (gl : G)}
termination_by g
decreasing_by form_wf

@[inherit_doc adjoint]
notation g"°" => adjoint g

recommended_spelling "adjoint" for "°" in [adjoint, «term_°»]

namespace Adjoint

variable {G : Type (u + 1)} [Form G]

@[simp]
theorem adjoint_zero_eq_star : ((0 : G)°) = !{{0} | {0}} := by
  unfold adjoint
  simp only [isEnd_zero, and_self, ↓reduceIte]

theorem adjoint_not_isEnd (g : G) (p : Player) : ¬(IsEnd p (g°)) := by
  unfold adjoint
  simp only [isEnd_def]
  by_cases h1 : moves .left g = ∅ ∧ moves .right g = ∅ <;> simp [h1, isEnd_def]
  all_goals by_cases h2 : moves .left g = ∅ <;> cases p
  all_goals by_cases h3 : moves .right g = ∅ <;> simp [h2, h3, isEnd_def]
  rw [not_and] at h1
  exact h1 h2 h3

theorem adjoint_not_isEndLike (g : G) (p : Player) : ¬(IsEndLike p (g°)) := by
  unfold adjoint
  simp only [isEnd_def]
  by_cases h1 : moves .left g = ∅ ∧ moves .right g = ∅ <;> simp [h1, isEnd_def]
  all_goals by_cases h2 : moves .left g = ∅ <;> cases p
  all_goals by_cases h3 : moves .right g = ∅ <;> simp [h2, h3, isEnd_def]
  rw [not_and] at h1
  exact h1 h2 h3

private theorem mem_leftMoves_mem_adjoint_rightMoves {g gl : G} (h1 : gl ∈ moves .left g) :
    gl° ∈ moves .right (g°) := by
  rw [adjoint, isEnd_def, isEnd_def]
  have h2 : g ≠ 0 := mem_moves_ne_zero h1
  by_cases h3 : moves .left g = ∅ <;> by_cases h4 : moves .right g = ∅ <;> simp [*]
  · simp [h3] at h1
  · simp [h3] at h1
  · use gl
  · use gl

private theorem mem_rightMoves_mem_adjoint_leftMoves {g gr : G} (h1 : gr ∈ moves .right g) :
    gr° ∈ moves .left (g°) := by
  rw [adjoint, isEnd_def, isEnd_def]
  have h2 : g ≠ 0 := mem_moves_ne_zero h1
  by_cases h3 : moves .left g = ∅ <;> by_cases h4 : moves .right g = ∅ <;> simp [*]
  · simp [h4] at h1
  · use gr
  · simp [h4] at h1
  · use gr

theorem mem_adjoint_mem_opposite {g gp : G} {p : Player}
    (h1 : gp ∈ moves p g) : gp° ∈ moves (-p) (g°) := by
  cases p
  · exact mem_leftMoves_mem_adjoint_rightMoves h1
  · exact mem_rightMoves_mem_adjoint_leftMoves h1

theorem mem_adjoint_exists_opposite {g gp : G} {p : Player} (h1 : gp ∈ moves p (g°))
    (h2 : ¬(IsEnd (-p) g)) : ∃ gnp ∈ moves (-p) g, gp = gnp° := by
  unfold adjoint at h1
  have h3 : g ≠ 0 := not_isEnd_ne_zero h2
  by_cases h4 : IsEnd p g <;> cases p
  any_goals rw [Player.neg_left] at h2
  any_goals rw [Player.neg_right] at h2
  all_goals
  · simp only [h4, h2, and_false, false_and, ↓reduceIte, moves_ofSets, Player.cases,
               Set.mem_range, Subtype.exists, exists_prop] at h1
    obtain ⟨gnp, h5, h6⟩ := h1
    use gnp
    exact And.symm ⟨Eq.symm h6, h5⟩

theorem mem_adjoint_end_opposite {g gp : G} {p : Player}
    (h1 : gp ∈ moves p (g°)) (h2 : IsEnd (-p) g) : gp = 0 := by
  unfold adjoint at h1
  by_cases h3 : IsEnd p g
  · cases p
    all_goals
    · simp only [Player.neg_left, Player.neg_right] at h2
      simp only [h2, h3, and_self, ↓reduceIte, moves_ofSets, Player.cases,
        Set.mem_singleton_iff] at h1
      exact h1
  · have h4 : g ≠ 0 := not_isEnd_ne_zero h3
    cases p
    all_goals
    · simp only [Player.neg_left, Player.neg_right] at h2
      simp only [h2, h3, and_true, and_false, ↓reduceIte, moves_ofSets, Player.cases,
        Set.mem_singleton_iff] at h1
      exact h1

/--
Adjoint of a short game is also short
-/
theorem short_adjoint {g : G} (h1 : IsShort g) : IsShort (g°) := by
  unfold adjoint
  by_cases hleft : IsEnd .left g
  · by_cases hright : IsEnd .right g
    · simp only [hleft, hright, and_self, ↓reduceIte, Short.star]
    · simp only [hleft, hright, and_false, ↓reduceIte]
      apply Short.ofSets
      · have : Finite (moves .right g) := Short.finite_moves .right h1
        exact Set.finite_range (fun gr : moves .right g => adjoint (gr : G))
      · intro gr hgr
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgr
        obtain ⟨gr', hgr', rfl⟩ := hgr
        exact short_adjoint (Short.of_mem_moves h1 hgr')
      · exact Set.finite_singleton 0
      · intro gr hgr
        simp only [Set.mem_singleton_iff] at hgr
        subst gr
        exact Short.zero
  · by_cases hright : IsEnd .right g
    · simp only [hleft, hright, and_true, ↓reduceIte]
      apply Short.ofSets
      · exact Set.finite_singleton 0
      · intro gl hgl
        simp only [Set.mem_singleton_iff] at hgl
        subst gl
        exact Short.zero
      · have : Finite (moves .left g) := Short.finite_moves .left h1
        exact Set.finite_range (fun gl : moves .left g => adjoint (gl : G))
      · intro gl hgl
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgl
        obtain ⟨gl', hgl', rfl⟩ := hgl
        exact short_adjoint (Short.of_mem_moves h1 hgl')
    · simp only [hleft, hright, and_self, ↓reduceIte]
      apply Short.ofSets
      · have : Finite (moves .right g) := Short.finite_moves .right h1
        exact Set.finite_range (fun gr : moves .right g => adjoint (gr : G))
      · intro gr hgr
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgr
        obtain ⟨gr', hgr', rfl⟩ := hgr
        exact short_adjoint (Short.of_mem_moves h1 hgr')
      · have : Finite (moves .left g) := Short.finite_moves .left h1
        exact Set.finite_range (fun gl : moves .left g => adjoint (gl : G))
      · intro gl hgl
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgl
        obtain ⟨gl', hgl', rfl⟩ := hgl
        exact short_adjoint (Short.of_mem_moves h1 hgl')
termination_by g
decreasing_by all_goals form_wf

open Classical in
protected theorem moves (p : Player) (g : G) :
    moves p (g°) = if IsEnd (-p) g then {(0 : G)} else ( · °) '' moves (-p) g := by
  rw [Form.adjoint]
  by_cases hl : IsEnd .left g <;> by_cases hr : IsEnd .right g <;> cases p <;>
    simp only [hl, hr, and_true, and_false, and_self, if_true, if_false,
      Player.neg_left, Player.neg_right, leftMoves_ofSets, rightMoves_ofSets,
      Set.image_eq_range]

/-- The adjoint of the conjugate is the conjugate of the adjoint. -/
theorem adjoint_neg (g : G) : (-g)° = -(g°) := by
  have key : ∀ p : Player,
      Set.range (fun x : moves p (-g) => ((x : G)°))
        = -Set.range (fun x : moves (-p) g => ((x : G)°)) := by
    intro p
    ext y
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_neg]
    rw [exists_moves_neg]
    refine exists_congr fun x => and_congr_right fun hx => ?_
    rw [adjoint_neg x]
    exact neg_eq_iff_eq_neg
  unfold adjoint
  by_cases hl : IsEnd .left g <;> by_cases hr : IsEnd .right g <;>
    simp only [IsEnd.neg_iff_neg, Player.neg_left, Player.neg_right, hl, hr, and_self,
      and_true, and_false, ↓reduceIte, neg_ofSets, Set.neg_singleton, neg_zero, key]
termination_by g
decreasing_by all_goals form_wf

end Adjoint

end Form
