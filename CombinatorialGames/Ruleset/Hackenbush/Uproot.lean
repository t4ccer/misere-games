/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Ruleset.Hackenbush
import Mathlib.Tactic.Cases

/-!
# Uproot Hackenbush

Uproot Hackenbush is played on the same positions as Hackenbush (a graph with
a ground vertex, blue/red/green edges, no green edge touching the ground).
Besides the usual move of cutting an edge of your own colour or a green
edge, a player may *uproot*: delete a ground edge of the *opponent's* colour,
provided the position has at least two ground edges. Everything disconnected
from the ground falls away as usual.

Uproot is a sacrifice: it spends a move to remove one of the opponent's
obligations. The proviso guarantees an uproot never empties the position;
without it a single red ground edge would force Left to move to `0` and lose.
Since the proviso reads the whole position, a disjunctive sum of two
positions is not a position, so the class of positions is not closed under
addition and the stride result is proved by `GameForm.hasStride_of_options`
rather than via ordinal sums.

Under misère play the strides of a position are its ground counts, exactly
as in Hackenbush (`hasStride_groundCount`), so uprooting never changes an
outcome (`misereOutcome_eq_hackenbush`) and the misère quotient is `ℤ`. Two
bare blue ground edges form `{1 | 1}`: the player with no obligations is
forced to uproot, lowering the opponent's stride, which is why the stride
definition compares the best move against the opponent's stride *candidate*.
-/

attribute [local instance] Classical.propDecidable

public noncomputable section

open Form
open Form.Misere.Outcome
open GameForm

variable {V : Type}

namespace Hackenbush

/--
The ground edges of a position, of either colour.
-/
def groundEdgeFinset (hack : Hackenbush V) : Finset (Sym2 V) :=
  hack.edgeFinset.filter fun e => hack.ground ∈ e

theorem mem_groundEdgeFinset_iff {hack : Hackenbush V} {e : Sym2 V} :
    e ∈ hack.groundEdgeFinset ↔ e ∈ hack.graph.edgeSet ∧ hack.ground ∈ e := by
  simp only [groundEdgeFinset, Finset.mem_filter, mem_edgeFinset]

namespace Uproot

/--
Player `p` may delete `e`: it is not of the opponent's colour, or it is a
ground edge and at least two ground edges exist.
-/
def CanRemove (hack : Hackenbush V) (p : Player) (e : Sym2 V) : Prop :=
  hack.coloring e ≠ Color.ofPlayer (-p) ∨ (hack.ground ∈ e ∧ 2 ≤ hack.groundEdgeFinset.card)

theorem canRemove_of_ne {hack : Hackenbush V} {p : Player} {e : Sym2 V}
    (hc : hack.coloring e ≠ Color.ofPlayer (-p)) : CanRemove hack p e :=
  Or.inl hc

theorem canRemove_of_eq {hack : Hackenbush V} {p : Player} {e : Sym2 V}
    (hc : hack.coloring e = Color.ofPlayer p) : CanRemove hack p e :=
  Or.inl (by rw [hc]; exact Color.ofPlayer_ne_ofPlayer_neg p)

theorem canRemove_of_ground {hack : Hackenbush V} (p : Player) {e : Sym2 V}
    (hg : hack.ground ∈ e) (h2 : 2 ≤ hack.groundEdgeFinset.card) : CanRemove hack p e :=
  Or.inr ⟨hg, h2⟩

/--
Some player may delete any edge.
-/
theorem exists_canRemove (hack : Hackenbush V) (e : Sym2 V) : ∃ p, CanRemove hack p e := by
  obtain ⟨p, hp⟩ := Color.exists_ne_ofPlayer_neg (hack.coloring e)
  exact ⟨p, canRemove_of_ne hp⟩

/--
Moves in Uproot Hackenbush.
-/
protected def moves (p : Player) (hack : Hackenbush V) : Set (Hackenbush V) :=
  {hack' | ∃ e ∈ hack.graph.edgeSet, CanRemove hack p e ∧ hack' = hack.remove e}

theorem mem_moves_iff {p : Player} {hack hack' : Hackenbush V} :
    hack' ∈ Uproot.moves p hack ↔
    ∃ e ∈ hack.graph.edgeSet, CanRemove hack p e ∧ hack' = hack.remove e := Iff.rfl

def _root_.GameGraph.uprootHackenbush : GameGraph (Hackenbush V) where
  moves := Uproot.moves

private theorem edgeCard_lt_of_mem_moves {a b : Hackenbush V} {p : Player}
    (h : a ∈ GameGraph.uprootHackenbush.moves p b) :
    a.edgeCard < b.edgeCard := by
  simp only [GameGraph.uprootHackenbush] at h
  obtain ⟨e, he, _, rfl⟩ := mem_moves_iff.mp h
  exact edgeCard_remove_lt b e he

instance : GameGraph.IsWellFounded (GameGraph.uprootHackenbush (V := V)) :=
  GameGraph.IsWellFounded.of_subrelation
    (InvImage (· < ·) (fun hack : Hackenbush V => hack.edgeCard))
    (fun _ _ _ h => edgeCard_lt_of_mem_moves h)

/--
Convert an Uproot Hackenbush position to a GameForm.
-/
def toGameForm (hack : Hackenbush V) : GameForm :=
  GameGraph.toForm (g := GameGraph.uprootHackenbush) hack

@[simp]
theorem moves_toGameForm (p : Player) (hack : Hackenbush V) :
    Form.moves p (toGameForm hack) = toGameForm '' (Uproot.moves p hack) := by
  simp only [toGameForm]
  rw [GameGraph.moves_toForm]
  rfl

theorem mem_moves_toGameForm_iff {p : Player} {hack : Hackenbush V} {g : GameForm} :
    g ∈ Form.moves p (toGameForm hack) ↔
    ∃ (e : Sym2 V) (_ : e ∈ hack.graph.edgeSet),
      CanRemove hack p e ∧ g = toGameForm (hack.remove e) := by
  rw [moves_toGameForm]
  constructor
  · rintro ⟨hack', h_hack', rfl⟩
    obtain ⟨e, he, hc, rfl⟩ := mem_moves_iff.mp h_hack'
    exact ⟨e, he, hc, rfl⟩
  · rintro ⟨e, he, hc, rfl⟩
    exact ⟨hack.remove e, mem_moves_iff.mpr ⟨e, he, hc, rfl⟩, rfl⟩

theorem toGameForm_remove_mem_moves {hack : Hackenbush V} {e : Sym2 V} {p : Player}
    (he : e ∈ hack.graph.edgeSet) (hc : CanRemove hack p e) :
    toGameForm (hack.remove e) ∈ Form.moves p (toGameForm hack) := by
  rw [mem_moves_toGameForm_iff]
  exact ⟨e, he, hc, rfl⟩

/--
The game form is zero iff the graph has no edges.
-/
theorem toGameForm_eq_zero_iff {hack : Hackenbush V} :
    toGameForm hack = 0 ↔ hack.graph = ⊥ := by
  refine ⟨?_, ?_⟩
  · intro h
    contrapose! h
    obtain ⟨e, he⟩ : ∃ e : Sym2 V, e ∈ hack.graph.edgeSet := by
      refine Set.nonempty_iff_ne_empty.mpr fun h' => h <| ?_
      ext
      simp only [SimpleGraph.edgeSet_eq_empty, h] at h'
    intro h
    obtain ⟨p, hp⟩ := exists_canRemove hack e
    have := toGameForm_remove_mem_moves he hp
    simp only [h, moves_zero, Set.mem_empty_iff_false] at this
  · intro h
    have h_empty_moves : ∀ p : Player, Uproot.moves p hack = ∅ := by
      intro p
      ext hack'
      simp only [Uproot.moves, h, SimpleGraph.edgeSet_bot,
                 Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false]
    convert GameGraph.toForm_def' (g := GameGraph.uprootHackenbush) hack
    simp only [zero_def, GameGraph.uprootHackenbush, h_empty_moves, Set.image_empty]

/--
A move by a player with no ground edges never empties the position.
-/
theorem remove_graph_ne_bot_of_groundCount_zero {hack : Hackenbush V} {p : Player} {e : Sym2 V}
    (he : e ∈ hack.graph.edgeSet) (hc : CanRemove hack p e) (hgc : hack.groundCount p = 0) :
    (hack.remove e).graph ≠ ⊥ := by
  obtain hc | ⟨_, h2⟩ := hc
  · exact move_not_zero_of_groundCount_zero he hc hgc
  · obtain ⟨e', he', hne⟩ := Finset.exists_mem_ne h2 e
    rw [mem_groundEdgeFinset_iff] at he'
    exact remove_graph_ne_bot_of_ground_edge he'.1 he'.2 hne

/-!
### Stride theory
-/

/--
When p has no ground edges, the position is solved for p.
-/
theorem isSolved_of_groundCount_zero {hack : Hackenbush V} {p : Player}
    (hgc : hack.groundCount p = 0) :
    GameForm.IsSolved p (toGameForm hack) := by
  induction' m : hack.edgeCard using Nat.strong_induction_on
    with m ih generalizing hack p
  have ih_remove : ∀ (e : Sym2 V) (he : e ∈ hack.graph.edgeSet),
      (hack.remove e).groundCount p = 0 →
      GameForm.IsSolved p (toGameForm (hack.remove e)) := by
    intro e he hgc'
    refine ih _ ?_ hgc' rfl
    subst m
    exact hack.edgeCard_remove_lt e he
  rw [GameForm.isSolved_def]
  refine ⟨?_, ?_, ?_⟩
  · intro h_mem
    obtain ⟨e, he, hc, heq⟩ := mem_moves_toGameForm_iff.mp h_mem
    exact remove_graph_ne_bot_of_groundCount_zero he hc hgc (toGameForm_eq_zero_iff.mp heq.symm)
  · intro hne0 h_end
    have hne : hack.graph ≠ ⊥ := fun h => hne0 (toGameForm_eq_zero_iff.mpr h)
    obtain ⟨e, he_mem, _, he_col⟩ := exists_neg_ground_edge hne hgc
    have hmove : toGameForm (hack.remove e) ∈ Form.moves (-p) (toGameForm hack) :=
      toGameForm_remove_mem_moves he_mem (canRemove_of_eq he_col)
    rw [Form.isEnd_def] at h_end
    rwa [h_end] at hmove
  · intro gp hopt
    rw [Form.isOption_iff_mem_union] at hopt
    obtain hopt | hopt := hopt
    all_goals
    · obtain ⟨e, he, _, rfl⟩ := mem_moves_toGameForm_iff.mp hopt
      exact ih_remove e he (groundCount_zero_of_option hgc)

/--
When `groundCount p ≥ 1`, the position is not solved for `p`.
-/
theorem not_isSolved_of_groundCount_pos {hack : Hackenbush V} {p : Player}
    (hgc : 1 ≤ hack.groundCount p) :
    ¬GameForm.IsSolved p (toGameForm hack) := by
  induction' n : hack.edgeCard using Nat.strong_induction_on
    with n ih generalizing hack p
  intro h_solved
  have ih_remove : ∀ (e : Sym2 V) (he : e ∈ hack.graph.edgeSet),
      1 ≤ (hack.remove e).groundCount p → CanRemove hack (-p) e → False := by
    intro e he hgc' hc
    refine ih _ ?_ hgc' rfl (GameForm.isSolved_of_mem_moves h_solved
      (toGameForm_remove_mem_moves he hc))
    subst n
    exact hack.edgeCard_remove_lt e he
  have hne : hack.graph ≠ ⊥ := by
    intro hbot
    rw [groundCount_eq_card] at hgc
    obtain ⟨e, he⟩ := Finset.card_pos.mp hgc
    rw [mem_groundEdges_iff, hbot] at he
    simp at he
  have hne0 : toGameForm hack ≠ 0 :=
    fun h => hne (toGameForm_eq_zero_iff.mp h)
  -- Case split: does (-p) have a cut?
  by_cases h_cut : ∃ e ∈ hack.graph.edgeSet, hack.coloring e ≠ Color.ofPlayer p
  · -- Case A: (-p) cuts e₁, which does not touch p's ground count
    obtain ⟨e₁, he₁, hc₁⟩ := h_cut
    refine ih_remove e₁ he₁ ?_ (canRemove_of_ne (by rwa [neg_neg]))
    rw [groundCount_remove_of_ne hc₁]
    exact hgc
  push_neg at h_cut
  by_cases h2 : 2 ≤ hack.groundEdgeFinset.card
  · -- Case B: all edges are p-coloured and there are two ground edges, so p has
    -- two ground edges and (-p) uproots one of them
    obtain ⟨e₀, he₀⟩ : (hack.groundEdges p).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      simp only [groundCount_eq_card, h_empty, Finset.card_empty, nonpos_iff_eq_zero,
        one_ne_zero] at hgc
    obtain ⟨e₁, he₁, hne₁⟩ := Finset.exists_mem_ne h2 e₀
    rw [mem_groundEdgeFinset_iff] at he₁
    have he₁_p : e₁ ∈ hack.groundEdges p :=
      mem_groundEdges_iff.mpr ⟨he₁.1, he₁.2, h_cut e₁ he₁.1⟩
    have h_two : 2 ≤ hack.groundCount p := by
      rw [groundCount_eq_card]
      exact Finset.one_lt_card.mpr ⟨e₁, he₁_p, e₀, he₀, hne₁⟩
    refine ih_remove e₁ he₁.1 ?_ (canRemove_of_ground (-p) he₁.2 h2)
    have := groundCount_remove_ge hack e₁ p
    omega
  · -- Case C: (-p) has no move at all, so the position is a nonzero (-p)-end
    refine absurd ?_ (GameForm.isSolved_not_isEnd h_solved hne0)
    rw [isEnd_def, moves_toGameForm, Set.image_eq_empty]
    ext
    simp only [Uproot.moves, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨e, he, hc | ⟨_, hc⟩, _⟩
    · rw [neg_neg] at hc
      exact hc (h_cut e he)
    · exact h2 hc

/--
The `p`-stride of an Uproot Hackenbush position equals the number of
`p`-coloured ground edges, exactly as in Hackenbush.
-/
theorem hasStride_groundCount (hack : Hackenbush V) (p : Player) :
    GameForm.HasStride p (toGameForm hack) (hack.groundCount p) := by
  induction' n : hack.edgeCard using Nat.strong_induction_on
    with n ih generalizing hack p
  have ih_remove : ∀ (e : Sym2 V) (he : e ∈ hack.graph.edgeSet) (q : Player),
      GameForm.HasStride q (toGameForm (hack.remove e))
        ((hack.remove e).groundCount q) := by
    intro e he q
    refine ih _ ?_ _ _ rfl
    subst n
    exact hack.edgeCard_remove_lt e he
  refine GameForm.hasStride_of_options (toGameForm hack) hack.groundCount ?_ ?_ ?_ ?_ ?_ p
  · intro q h_zero
    exact isSolved_of_groundCount_zero h_zero
  · intro q h_ne_zero
    exact not_isSolved_of_groundCount_pos (by omega)
  · intro q g' hg'
    obtain ⟨e, he, _, rfl⟩ := mem_moves_toGameForm_iff.mp hg'
    have hge := groundCount_remove_ge hack e q
    exact ⟨(hack.remove e).groundCount q, by omega, ih_remove e he q⟩
  · intro q h_ne_zero
    have ⟨e₀, he₀⟩ : (hack.groundEdges q).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      simp only [groundCount_eq_card, h_empty, Finset.card_empty, ne_eq, not_true_eq_false]
        at h_ne_zero
    obtain ⟨he₀_mem, he₀_gnd, he₀_col⟩ := mem_groundEdges_iff.mp he₀
    refine ⟨toGameForm (hack.remove e₀),
      toGameForm_remove_mem_moves he₀_mem (canRemove_of_eq he₀_col), ?_, ?_⟩
    · rw [← groundCount_remove_ground he₀_mem he₀_gnd he₀_col]
      exact ih_remove e₀ he₀_mem q
    · rw [← groundCount_remove_of_ne (p := -q)
        (by rw [he₀_col]; exact Color.ofPlayer_ne_ofPlayer_neg q)]
      exact ih_remove e₀ he₀_mem (-q)
  · intro q g' hg'
    obtain ⟨e, he, _, rfl⟩ := mem_moves_toGameForm_iff.mp hg'
    exact ⟨(hack.remove e).groundCount q, groundCount_remove_le hack e q, ih_remove e he q⟩

/--
Uprooting never changes an outcome.
-/
theorem misereOutcome_eq_hackenbush (hack : Hackenbush V) :
    MisereOutcome (toGameForm hack) = MisereOutcome hack.toGameForm :=
  misereOutcome_eq_of_hasStride (hasStride_groundCount hack .left)
    (hasStride_groundCount hack .right) (Hackenbush.hasStride_groundCount hack .left)
    (Hackenbush.hasStride_groundCount hack .right)

/--
Uproot Hackenbush as a ruleset. This is a different `Ruleset` structure on
the same position type as Hackenbush, so it is not an instance.
-/
def ruleset : Ruleset (Hackenbush V) where
  toGameForm := toGameForm
  moves_toGameForm p r g' h_g' := by
    simp only [moves_toGameForm, Set.mem_image] at h_g'
    obtain ⟨r', _, h_r'⟩ := h_g'
    use r'

/--
The game forms of Uproot Hackenbush positions.
-/
def Forms (V : Type) (g : GameForm) : Prop :=
  ∃ hack : Hackenbush V, g = toGameForm hack

instance : Hereditary (Forms V) where
  has_option h_g h_g' := by
    obtain ⟨hack, rfl⟩ := h_g
    rw [isOption_iff_mem_moves] at h_g'
    obtain ⟨p, h_g'⟩ := h_g'
    obtain ⟨e, _, _, rfl⟩ := mem_moves_toGameForm_iff.mp h_g'
    exact ⟨hack.remove e, rfl⟩

instance : GameForm.Strided (Forms ℕ) where
  mk_with_strides l r := by
    refine ⟨toGameForm (starPos l r), ⟨starPos l r, rfl⟩, ?_, ?_⟩
    · convert hasStride_groundCount (starPos l r) .left
      rw [starPos_groundCount_left l r]
    · convert hasStride_groundCount (starPos l r) .right
      rw [starPos_groundCount_right l r]
  has_stride p g hg := by
    obtain ⟨hack, rfl⟩ := hg
    exact ⟨_, hasStride_groundCount hack p⟩

protected def equivInt : MisereQuotient (Forms ℕ) ≃ ℤ :=
  MisereQuotient.stridedEquivInt

protected def closure.equivInt : MisereQuotient (ClosedUnderAdd.closure (Forms ℕ)) ≃ ℤ :=
  MisereQuotient.stridedEquivInt

end Uproot

end Hackenbush
