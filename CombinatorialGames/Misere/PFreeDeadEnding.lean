/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.DeadEnding

/-!
# $\mathscr{P}$-free dead-ending games

The main results are
* `misereGE_of_int_le`
* `isEnd_exists_intCast_misereEQ`
-/

public section

universe u

open Form
open Form.Misere.Outcome
open GameForm
open PFree

private theorem misereOutcome_ofPlayer_of_not_winsGoingFirst {p : Player} {g : GameForm}
    (h_pfree : IsPFree g) (h_not : ¬WinsGoingFirst (-p) g) : MisereOutcome g = Outcome.ofPlayer p := by
  rw [misereOutcome_eq_player_iff]
  refine ⟨?_, h_not⟩
  by_contra h_not'
  exact misereOutcome_ne_P_of_pfree h_pfree (misereOutcome_P_iff_winsGoingFirst'.mpr ⟨h_not', h_not⟩)

private theorem eq_zero_of_misereOutcome' {p : Player} {g : GameForm} (hg : IsDeadEnding g)
    (hN : MisereOutcome g = .N) (h_end : IsEnd p g) : g = 0 := by
  cases p
  · exact DeadEnding.eq_zero_of_misereOutcome hg hN h_end
  · have := DeadEnding.eq_zero_of_misereOutcome (ClosedUnderNeg.neg_of hg)
      (misereOutcome_neg_N_iff_misereOutcome.mpr hN) (IsEnd.neg_iff_neg.mpr h_end)
    rwa [neg_eq_zero] at this

mutual

private theorem misereOutcome_of_add_ofPlayer.aux {p : Player} {g h : GameForm}
    (hg : (PFreeSubset IsDeadEnding) g) (hh : (PFreeSubset IsDeadEnding) h)
    (hgL : MisereOutcome g = Outcome.ofPlayer p) (hhL : MisereOutcome h = Outcome.ofPlayer p) :
    MisereOutcome (g + h) = Outcome.ofPlayer p := by
  have hg_out := (misereOutcome_eq_player_iff _ _).mp hgL
  have hh_out := (misereOutcome_eq_player_iff _ _).mp hhL
  rw [misereOutcome_eq_player_iff]
  constructor
  · rcases (winsGoingFirst_iff g p).mp hg_out.left with
        hg_end | ⟨gl, hgl, hgl_not_right⟩
    · rcases (winsGoingFirst_iff h p).mp hh_out.left with
          hh_end | ⟨hl, hhl, hhl_not_right⟩
      · exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨isEndLike_iff_isEnd.mp hg_end, isEndLike_iff_isEnd.mp  hh_end⟩)
      · have hhl_pfde := Hereditary.of_mem_moves hh hhl
        have hhlL := misereOutcome_ofPlayer_of_not_winsGoingFirst hhl_pfde.isPFree hhl_not_right
        have hsumL := misereOutcome_of_add_ofPlayer.aux hg hhl_pfde hgL hhlL
        exact winsGoingFirst_of_moves
          ⟨g + hl, add_left_mem_moves_add hhl g, ((misereOutcome_eq_player_iff _ _).mp hsumL).right⟩
    · have hgl_pfde := Hereditary.of_mem_moves hg hgl
      have hglL := misereOutcome_ofPlayer_of_not_winsGoingFirst hgl_pfde.isPFree hgl_not_right
      have hsumL := misereOutcome_of_add_ofPlayer.aux hgl_pfde hh hglL hhL
      exact winsGoingFirst_of_moves
        ⟨gl + h, add_right_mem_moves_add hgl h, ((misereOutcome_eq_player_iff _ _).mp hsumL).right⟩
  · rw [not_winsGoingFirst_iff, neg_neg]
    refine ⟨fun h_end => ?_, fun gr hgr => ?_⟩
    · exact hg_out.right (winsGoingFirst_of_isEnd (IsEnd.add_iff.mp (isEndLike_iff_isEnd.mp  h_end)).left)
    · rw [moves_add, Set.mem_union, Set.mem_image] at hgr
      rcases hgr with ⟨gr', hgr', rfl⟩ | ⟨hr, hhr, rfl⟩
      · have h_left_gr' : WinsGoingFirst p gr' := by
          simpa using (not_winsGoingFirst_iff.mp hg_out.right).right gr' hgr'
        have hgr_pfde := Hereditary.of_mem_moves hg hgr'
        cases hgr'_out : MisereOutcome gr' with
        | L =>
            cases p
            · exact ((misereOutcome_eq_player_iff _ _).mp
                (misereOutcome_of_add_ofPlayer.aux (p := .left) hgr_pfde hh hgr'_out hhL)).left
            · exact absurd h_left_gr' (misereOutcome_L_iff_winsGoingFirst.mp hgr'_out).right
        | N =>
            have hwin : WinsGoingFirst p (h + gr') :=
              miserePlayerOutcome_eq_iff_winsGoingFirst.mp
                (miserePlayerOutcome_of_add_ofPlayer.aux hh hgr_pfde hhL hgr'_out)
            rwa [add_comm] at hwin
        | P => exact absurd hgr'_out (misereOutcome_ne_P_of_pfree hgr_pfde)
        | R =>
            cases p
            · exact absurd h_left_gr' (misereOutcome_R_iff_winsGoingFirst.mp hgr'_out).right
            · exact ((misereOutcome_eq_player_iff _ _).mp
                (misereOutcome_of_add_ofPlayer.aux (p := .right) hgr_pfde hh hgr'_out hhL)).left
      · have h_left_hr : WinsGoingFirst p hr := by
          simpa using (not_winsGoingFirst_iff.mp hh_out.right).right hr hhr
        have hhr_pfde := Hereditary.of_mem_moves hh hhr
        cases hhr_out : MisereOutcome hr with
        | L =>
            cases p
            · exact ((misereOutcome_eq_player_iff _ _).mp
                (misereOutcome_of_add_ofPlayer.aux (p := .left) hg hhr_pfde hgL hhr_out)).left
            · exact absurd h_left_hr (misereOutcome_L_iff_winsGoingFirst.mp hhr_out).right
        | N =>
            exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp
              (miserePlayerOutcome_of_add_ofPlayer.aux hg hhr_pfde hgL hhr_out)
        | P => exact absurd hhr_out (misereOutcome_ne_P_of_pfree hhr_pfde)
        | R =>
            cases p
            · exact absurd h_left_hr (misereOutcome_R_iff_winsGoingFirst.mp hhr_out).right
            · exact ((misereOutcome_eq_player_iff _ _).mp
                (misereOutcome_of_add_ofPlayer.aux (p := .right) hg hhr_pfde hgL hhr_out)).left
termination_by Form.birthday g + Form.birthday h
decreasing_by all_goals gameform_birthday

private theorem miserePlayerOutcome_of_add_ofPlayer.aux {p : Player} {g h : GameForm}
    (hg : (PFreeSubset IsDeadEnding) g) (hh : (PFreeSubset IsDeadEnding) h)
    (hgL : MisereOutcome g = Outcome.ofPlayer p) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) p = p := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst]
  by_cases h_zero : h = 0
  · subst h
    simpa [add_zero] using ((misereOutcome_eq_player_iff _ _).mp hgL).left
  · have h_not_end : ¬IsEnd p h :=
      fun h_end => h_zero (eq_zero_of_misereOutcome' hh.mem hhN h_end)
    rcases (winsGoingFirst_iff h p).mp (misereOutcome_N_iff_winsGoingFirst'.mp hhN).left with
        h_end | ⟨hl, hhl, hhl_not_right⟩
    · exact absurd (isEndLike_iff_isEnd.mp h_end) h_not_end
    · have hhl_pfde := Hereditary.of_mem_moves hh hhl
      refine winsGoingFirst_of_moves ⟨g + hl, add_left_mem_moves_add hhl g, ?_⟩
      refine ((misereOutcome_eq_player_iff _ _).mp ?_).right
      apply misereOutcome_of_add_ofPlayer.aux hg hhl_pfde hgL
      exact misereOutcome_ofPlayer_of_not_winsGoingFirst hhl_pfde.isPFree hhl_not_right
termination_by Form.birthday g + Form.birthday h
decreasing_by gameform_birthday

end

instance : OutcomeStable (IsDeadEnding (G := GameForm)) where
  misereOutcome_of_add_ofPlayer := misereOutcome_of_add_ofPlayer.aux
  miserePlayerOutcome_of_add_ofPlayer := miserePlayerOutcome_of_add_ofPlayer.aux

abbrev PFreeDeadEnding (g : GameForm) : Prop := (PFreeSubset DeadEnding.ShortDeadEnding) g

instance : DeadEnding PFreeDeadEnding where
  isDeadEnding h := h.mem.dead_ending

instance : Short PFreeDeadEnding where
  isShort h := h.mem.short

instance : OutcomeStable (DeadEnding.ShortDeadEnding (G := GameForm)) where
  misereOutcome_of_add_ofPlayer hg hh hgL hhL := misereOutcome_of_add_ofPlayer.aux
    (.mk hg.mem.dead_ending hg.isPFree) (.mk hh.mem.dead_ending hh.isPFree) hgL hhL
  miserePlayerOutcome_of_add_ofPlayer hg hh hgL hhN := miserePlayerOutcome_of_add_ofPlayer.aux
    (.mk hg.mem.dead_ending hg.isPFree) (.mk hh.mem.dead_ending hh.isPFree) hgL hhN

instance : ClosedUnderAddNat (DeadEnding.ShortDeadEnding (G := GameForm)) where
  has_add h_g n :=
    { dead_ending := DeadEnding.IsDeadEnding.add h_g.dead_ending (DeadEnding.isDeadEnding_natCast n)
    , short := IsShort.add (h_g.short) (IsShort.natCast n)
    }

instance : ClosedUnderAdd (DeadEnding.ShortDeadEnding (G := GameForm)) where
  has_add _ _  h_g h_h :=
    { dead_ending := DeadEnding.IsDeadEnding.add h_g.dead_ending h_h.dead_ending
    , short := IsShort.add h_g.short h_h.short
    }

instance : ClosedUnderAdd PFreeDeadEnding where
  has_add g h h_g h_h := by
    apply PFreeSubset.mk
    · exact ClosedUnderAdd.has_add g h h_g.mem h_h.mem
    · exact IntegerInvertible.isPFree_of_propertyX h_g h_h (Short.isShort h_g) (Short.isShort h_h)

namespace PFreeDeadEnding

theorem misereGE_of_int_le (a b : ℤ) (h1 : a ≥ b) : b ≥m PFreeDeadEnding a :=
  OutcomeStable.misereGE_of_int_le _ b a h1

theorem misereGE_of_nat_le (a b : ℕ) (h1 : a ≥ b) : b ≥m PFreeDeadEnding a :=
  OutcomeStable.misereGE_of_nat_le _ b a h1

-- TODO: Move and maybe even @[simp]
theorem misereOutcome_ne_P_iff_winsGoingFirst {g : GameForm} :
    (MisereOutcome g ≠ .P) ↔ (WinsGoingFirst .right g ∨ WinsGoingFirst .left g) := by
  have := (misereOutcome_P_iff_winsGoingFirst (g := g)).not
  tauto

-- TODO: Move
@[simp]
theorem Set.insert_ne_empty {A : Type*} (x : A) (xs : Set A) : insert x xs ≠ ∅ := by
  simp [<-Set.nonempty_iff_ne_empty']

-- TODO: Move
theorem not_isEnd_nonempty {p : Player} {g : GameForm} (h1 : ¬ IsEnd p g) : Nonempty (moves p g) := by
  rw [isEnd_def] at h1
  exact Set.nonempty_iff_ne_empty'.mpr h1

theorem misereGE_of_maintenance_proviso
    {g h : GameForm} (hg : IsPFree g) (hh : IsPFree h)
    (h_m_r : Maintenance PFreeDeadEnding g h .right) (h_m_l : Maintenance PFreeDeadEnding g h .left)
    (h_p_r : IsEnd .right g → MisereOutcome h ≠ .L) (h_p_l : IsEnd .left h → MisereOutcome g ≠ .R)
    : g ≥m PFreeDeadEnding h := by
  refine Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding h_m_r h_m_l ?_ ?_
  · intro h_isEnd
    rw [GameForm.isEndLike_iff_isEnd] at h_isEnd
    rw [PFree.strong_iff_misereOutcome hh]
    exact h_p_r h_isEnd
  · intro h_isEnd
    rw [GameForm.isEndLike_iff_isEnd] at h_isEnd
    rw [PFree.strong_iff_misereOutcome hg]
    exact h_p_l h_isEnd

-- TODO: Move
@[simp]
theorem isEnd_ofSets {p : Player}
    {st : Player → Set GameForm} [Small (st .left)] [Small (st .right)] :
  IsEnd p !{st} ↔ (st p = ∅) := by
  simp [isEnd_def]

lemma strong_left_of_misereOutcome_L {A : GameForm → Prop} [PFree A] [OutcomeStable A] {g : GameForm}
    (h1 : (PFreeSubset A) g) (h2 : MisereOutcome g = .L) : Strong (PFreeSubset A) g .left := by
  intro x hx h3
  apply Or.elim (misereOutcome_of_isEnd_left hx (isEndLike_iff_isEnd.mp h3)) <;> intro h5
  · apply Or.elim (OutcomeStable.misereOutcome_of_add_ofPlayer_N (p := .left) h1 hx h2 h5) <;> intro h6
    · rw [<-miserePlayerOutcome_eq_iff_winsGoingFirst]
      exact (misereOutcome_N_iff_miserePlayerOutcome.mp h6).left
    · exact minsGoingFirst_left_of_misereOutcome_L h6
  · exact minsGoingFirst_left_of_misereOutcome_L
      (OutcomeStable.misereOutcome_of_add_ofPlayer (p := .left) h1 hx h2 h5)

lemma strong_right_of_misereOutcome_R {A : GameForm → Prop} [PFree A] [OutcomeStable A] {g : GameForm}
    (h1 : (PFreeSubset A) g) (h2 : MisereOutcome g = .R) : Strong (PFreeSubset A) g .right := by
  intro x hx h3
  apply Or.elim (misereOutcome_of_isEnd_right hx (isEndLike_iff_isEnd.mp h3)) <;> intro h5
  · apply Or.elim (OutcomeStable.misereOutcome_of_add_ofPlayer_N (p := .right) h1 hx h2 h5) <;> intro h6
    · rw [<-miserePlayerOutcome_eq_iff_winsGoingFirst]
      exact (misereOutcome_N_iff_miserePlayerOutcome.mp h6).right
    · exact winsGoingFirst_right_of_misereOutcome_R h6
  · exact winsGoingFirst_right_of_misereOutcome_R
      (OutcomeStable.misereOutcome_of_add_ofPlayer (p := .right) h1 hx h2 h5)

private theorem misereEQ_intCast_pred_of_options {g : GameForm.{u}} (n : ℤ) (hn : n ≤ 0)
    (h_isEnd : IsEnd .left g)
    (h_all_ge : ∀ gr ∈ moves .right g, gr ≥m PFreeDeadEnding ((n : ℤ) : GameForm))
    (h_exists_n : ∃ gr ∈ moves .right g, ((n : ℤ) : GameForm) ≥m PFreeDeadEnding gr) :
    g =m PFreeDeadEnding ((n - 1 : ℤ) : GameForm) := by
  have hRM : moves .right ((n - 1 : ℤ) : GameForm.{u}) = {((n : ℤ) : GameForm.{u})} := by
    have key : ((n - 1 : ℤ)) = -((1 - n : ℤ)) := by omega
    rw [key, Form.intCast_neg, moves_neg, Player.neg_right, leftMoves_intCast (by omega),
       show ((1 - n : ℤ) - 1) = -n by omega, Form.intCast_neg, Set.neg_singleton, neg_neg]
  have hL0 : moves .left ((n - 1 : ℤ) : GameForm.{u}) = ∅ := by
    have := isEnd_of_isDeadEnd (isDeadEnd_left_nonpos_intCast (G := GameForm.{u}) (n - 1) (by omega))
    rwa [isEnd_def] at this
  have hLg : moves .left g = ∅ := by rwa [isEnd_def] at h_isEnd
  have hEnd_h : IsEnd .left ((n - 1 : ℤ) : GameForm.{u}) :=
    isEnd_of_isDeadEnd (isDeadEnd_left_nonpos_intCast (G := GameForm.{u}) (n - 1) (by omega))
  have hge : g ≥m PFreeDeadEnding ((n - 1 : ℤ) : GameForm) := by
    apply Form.Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding
    · intro gr hgr
      exact Or.inl ⟨((n : ℤ) : GameForm), by rw [hRM]; rfl, h_all_ge gr hgr⟩
    · intro hl hhl; rw [hL0] at hhl; exact absurd hhl (Set.notMem_empty _)
    · intro hcontra
      obtain ⟨gr, hgr, _⟩ := h_exists_n
      rw [GameForm.isEndLike_iff_isEnd, isEnd_def] at hcontra
      rw [hcontra] at hgr; exact absurd hgr (Set.notMem_empty _)
    · exact fun _ => strong_of_isEnd h_isEnd
  have hle : ((n - 1 : ℤ) : GameForm) ≥m PFreeDeadEnding g := by
    apply Form.Hereditary.misereGE_of_maintenance_proviso PFreeDeadEnding
    · intro hr hhr
      rw [hRM, Set.mem_singleton_iff] at hhr
      obtain ⟨gr, hgr, hgex⟩ := h_exists_n
      exact Or.inl ⟨gr, hgr, by rw [hhr]; exact hgex⟩
    · intro gl hgl; rw [hLg] at hgl; exact absurd hgl (Set.notMem_empty _)
    · intro hcontra
      rw [GameForm.isEndLike_iff_isEnd, isEnd_def, hRM] at hcontra
      exact absurd hcontra (by simp)
    · exact fun _ => strong_of_isEnd hEnd_h
  exact MisereEq.of_antisymm hge hle

private theorem exists_intCast_of_options_misereEQ {g : GameForm.{u}}
    (h_isEnd_left : IsEnd .left g) (h_not_isEnd_right : ¬IsEnd .right g)
    (h_mem_right : ∀ gr ∈ moves .right g, ∃ n : ℕ, gr =m PFreeDeadEnding ((-(n : ℤ) : ℤ) : GameForm)) :
    ∃ n : ℕ, g =m PFreeDeadEnding ((-(n : ℤ) : ℤ) : GameForm) := by
  set S := {n : ℕ | ∃ gr ∈ moves Player.right g, gr =m PFreeDeadEnding ((-(n : ℤ) : ℤ) : GameForm)}
    with hS_def
  have h_S_nonempty : S.Nonempty := by
    have : (moves .right g).Nonempty := by
      rw [isEnd_def] at h_not_isEnd_right
      exact Set.nonempty_iff_empty_ne.mpr fun a ↦ h_not_isEnd_right (Eq.symm a)
    exact this.elim fun x hx => (h_mem_right x hx).elim fun a ha => ⟨a, x, hx, ha⟩
  set M := sInf S with hM_def
  obtain ⟨gr0, h_gr0_mem, h_gr0_eq⟩ :
      ∃ gr0 ∈ moves Player.right g, gr0 =m PFreeDeadEnding ((-(M : ℤ) : ℤ) : GameForm) :=
    Nat.sInf_mem h_S_nonempty
  have h_M_le : ∀ a ∈ S, M ≤ a := fun a ha => Nat.sInf_le ha
  have h_misereEQ : g =m PFreeDeadEnding ((-(M : ℤ) - 1 : ℤ) : GameForm) := by
    refine misereEQ_intCast_pred_of_options ((-(M : ℤ) : ℤ)) (by omega) h_isEnd_left ?_
      ⟨gr0, h_gr0_mem, misereGE_of_misereEQ h_gr0_eq.symm⟩
    intro gr h_gr_mem
    obtain ⟨a, ha⟩ := h_mem_right gr h_gr_mem
    have h_M_le_a : M ≤ a := h_M_le a ⟨gr, h_gr_mem, ha⟩
    rw [misereGE_rw_left_iff ha]
    exact PFreeDeadEnding.misereGE_of_int_le (-M : ℤ) (-a : ℤ) (by omega)
  exact ⟨M + 1, by simpa [neg_add_eq_sub] using h_misereEQ⟩

/--
If $G \in \operatorname{pf}(\mathcal{E})$ is a Left end,
then it is equivalent to some non-positive integer.
-/
private theorem isEnd_left_exists_intCast_misereEQ {g : GameForm}
    (h_g : PFreeDeadEnding g) (h_isEnd_left : IsEnd .left g) :
    ∃ n : ℕ, g =m PFreeDeadEnding ((-(n : ℤ) : ℤ) : GameForm) := by
  by_cases h_isEnd_right : IsEnd .right g
  · use 0
    have h_g_eq_zero : g = 0 := both_ends_eq_zero h_isEnd_left h_isEnd_right
    subst h_g_eq_zero
    intro x _
    simp
  · have h_isDeadEnd_g := isDeadEnd_of_isDeadEnding (DeadEnding.isDeadEnding h_g) h_isEnd_left
    have h_opt : ∀ gr ∈ moves .right g,
        ∃ n : ℕ, gr =m PFreeDeadEnding ((-(n : ℤ) : ℤ) : GameForm) := by
      intro gr h_gr
      have h_pf_deadEnding_gr := Hereditary.of_mem_moves h_g h_gr
      have h_isEnd_gr := isEnd_of_isDeadEnd (isDeadEnd_of_mem_moves h_isDeadEnd_g h_gr)
      exact isEnd_left_exists_intCast_misereEQ h_pf_deadEnding_gr h_isEnd_gr
    exact exists_intCast_of_options_misereEQ h_isEnd_left h_isEnd_right h_opt
termination_by g
decreasing_by form_wf

/--
If $G \in \operatorname{pf}(\mathcal{E})$ is a Right end,
then it is equivalent to some non-negative integer.
-/
theorem isEnd_right_exists_intCast_misereEQ {g : GameForm}
    (h_g : PFreeDeadEnding g) (h_isEnd : IsEnd .right g) :
    ∃ n : ℕ, g =m PFreeDeadEnding ((n : ℤ) : GameForm) := by
  obtain ⟨n, ha⟩ := isEnd_left_exists_intCast_misereEQ
      (ClosedUnderNeg.neg_of h_g) (IsEnd.neg_iff_neg.mpr h_isEnd)
  use n
  rwa [Form.intCast_neg n, misereEQ_neg_iff] at ha

/--
If $G \in \operatorname{pf}(\mathcal{E})$ is an end,
then it is equivalent to some integer.
-/
theorem isEnd_exists_intCast_misereEQ {p : Player} {g : GameForm} (h_g : PFreeDeadEnding g)
    (h_isEnd : IsEnd p g) :
    ∃ k : ℤ, g =m PFreeDeadEnding ((k : ℤ) : GameForm) := by
  cases p
  · obtain ⟨a, ha⟩ := isEnd_left_exists_intCast_misereEQ h_g h_isEnd
    exact ⟨-(a : ℤ), ha⟩
  · obtain ⟨a, ha⟩ := isEnd_right_exists_intCast_misereEQ h_g h_isEnd
    exact ⟨(a : ℤ), ha⟩
