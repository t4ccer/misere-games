module

public import CombinatorialGames.Form.Misere.Adjoint
public import CombinatorialGames.Misere.Hereditary

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Form.Misere.Adjoint
open Form.Misere.Outcome

public section

namespace Form

@[expose] def Downlinked (A : G → Prop) (g h : G) : Prop :=
  ∃ t, A t ∧ ¬WinsGoingFirst .left (g + t) ∧
    ¬WinsGoingFirst .right (h + t)

@[expose] def Separating (A : G → Prop) (p : Player) (g h : G) : Prop :=
  match p with
  | .left => ∃ x, A x ∧ ¬WinsGoingFirst .left (g + x) ∧
      WinsGoingFirst .left (h + x)
  | .right => ∃ x, A x ∧ WinsGoingFirst .right (g + x) ∧
      ¬WinsGoingFirst .right (h + x)

abbrev LeftSeparating (A : G → Prop) (g h : G) : Prop :=
  Separating A .left g h

abbrev RightSeparating (A : G → Prop) (g h : G) : Prop :=
  Separating A .right g h

theorem Downlinked.not_exists_left_right_misere_ge {A : G → Prop} {g h : G}
    (h_downlinked : Downlinked A g h) :
    (¬∃ gl ∈ moves .left g, gl ≥m A h) ∧
      (¬∃ hr ∈ moves .right h, g ≥m A hr) := by
  obtain ⟨t, ht, hgt, hht⟩ := h_downlinked
  constructor
  · rintro ⟨gl, hgl, hge⟩
    rw [not_WinsGoingFirst] at hgt
    have hgl_out : MiserePlayerOutcome (gl + t) .right = .right :=
      MiserePlayerOutcome_eq_iff_WinsGoingFirst.mpr
        (hgt.right (gl + t) (add_right_mem_moves_add hgl t))
    have hht_out : MiserePlayerOutcome (h + t) .right = .left := by
      unfold MiserePlayerOutcome
      simp [hht]
    have h_cmp := MisereOutcome_ge_iff_MiserePlayerOutcome_ge.mp (hge t ht) .right
    rw [hgl_out, hht_out] at h_cmp
    exact Player.left_le_right h_cmp
  · rintro ⟨hr, hhr, hge⟩
    rw [not_WinsGoingFirst] at hht
    have hhr_out : MiserePlayerOutcome (hr + t) .left = .left :=
      MiserePlayerOutcome_eq_iff_WinsGoingFirst.mpr
        (hht.right (hr + t) (add_right_mem_moves_add hhr t))
    have hgt_out : MiserePlayerOutcome (g + t) .left = .right := by
      unfold MiserePlayerOutcome
      simp [hgt]
    have h_cmp := MisereOutcome_ge_iff_MiserePlayerOutcome_ge.mp (hge t ht) .left
    rw [hgt_out, hhr_out] at h_cmp
    exact Player.left_le_right h_cmp

theorem leftSeparating_or_rightSeparating_of_not_misere_ge {U : G → Prop}
    {g h : G} (h_not_ge : ¬(g ≥m U h)) :
    LeftSeparating U g h ∨ RightSeparating U g h := by
  rw [MisereGe] at h_not_ge
  simp only [not_forall] at h_not_ge
  obtain ⟨x, hx, h_not_outcome_ge⟩ := h_not_ge
  have h_not_player_ge :
      ¬∀ p, MiserePlayerOutcome (g + x) p ≥ MiserePlayerOutcome (h + x) p := by
    intro h_player_ge
    exact h_not_outcome_ge (MisereOutcome_ge_iff_MiserePlayerOutcome_ge.mpr h_player_ge)
  simp only [Player.forall, not_and_or] at h_not_player_ge
  cases h_not_player_ge with
  | inl h_left =>
      left
      cases hg : MiserePlayerOutcome (g + x) .left
      <;> cases hh : MiserePlayerOutcome (h + x) .left
      <;> simp [hg, hh] at h_left
      refine ⟨x, hx, ?_, ?_⟩
      · intro h_win
        have h_out := MiserePlayerOutcome_eq_iff_WinsGoingFirst.mpr h_win
        rw [hg] at h_out
        cases h_out
      · exact MiserePlayerOutcome_eq_iff_WinsGoingFirst.mp hh
  | inr h_right =>
      right
      cases hg : MiserePlayerOutcome (g + x) .right
      <;> cases hh : MiserePlayerOutcome (h + x) .right
      <;> simp [hg, hh] at h_right
      refine ⟨x, hx, ?_, ?_⟩
      · exact MiserePlayerOutcome_eq_iff_WinsGoingFirst.mp hg
      · intro h_win
        have h_out := MiserePlayerOutcome_eq_iff_WinsGoingFirst.mpr h_win
        rw [hh] at h_out
        cases h_out

namespace Separation

abbrev rightSeparatorLeftSet (h : G) : Set G :=
  {0} ∪ Set.range (fun hr : moves .right h => (hr : G)°)

noncomputable abbrev rightSeparatorCandidate (h x : G) : G :=
  !{rightSeparatorLeftSet h | {x}}

theorem rightSeparating_of_leftSeparating_of_rightSeparatorCandidate_mem
    {U : G → Prop} {g h : G}
    (h_candidate : ∀ {x : G}, U x → U (rightSeparatorCandidate h x))
    (h_left_sep : LeftSeparating U g h) :
    RightSeparating U g h := by
  obtain ⟨x, hx, hgx, hhx⟩ := h_left_sep
  let y := rightSeparatorCandidate h x
  have hy : U y := h_candidate hx
  refine ⟨y, hy, ?_, ?_⟩
  · apply WinsGoingFirst_of_moves
    refine ⟨g + x, ?_, ?_⟩
    · apply add_left_mem_moves_add
      change x ∈ moves .right (rightSeparatorCandidate h x)
      unfold rightSeparatorCandidate
      rw [rightMoves_ofSets (s := rightSeparatorLeftSet h) (t := {x})]
      simp only [Set.mem_singleton_iff]
    · exact hgx
  · rw [not_WinsGoingFirst]
    constructor
    · intro h_end
      have hy_end : IsEndLike .right y := (IsEndLike.add_iff.mp h_end).right
      change IsEndLike .right (rightSeparatorCandidate h x) at hy_end
      unfold rightSeparatorCandidate at hy_end
      rw [ofSets_IsEndLike_iff
        (s := rightSeparatorLeftSet h) (t := {x}),
        IsEnd_def] at hy_end
      rw [rightMoves_ofSets (s := rightSeparatorLeftSet h) (t := {x})] at hy_end
      exact Set.singleton_ne_empty x hy_end
    · intro k hk
      rw [moves_add] at hk
      cases hk with
      | inl h_h_move =>
          obtain ⟨hr, hhr, rfl⟩ := h_h_move
          apply WinsGoingFirst_of_moves
          refine ⟨hr + hr°, ?_, ?_⟩
          · apply add_left_mem_moves_add
            change hr° ∈ moves .left (rightSeparatorCandidate h x)
            unfold rightSeparatorCandidate
            rw [leftMoves_ofSets (s := rightSeparatorLeftSet h) (t := {x})]
            simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
            right
            exact ⟨⟨hr, hhr⟩, rfl⟩
          · exact not_WinsGoingFirst_of_MisereOutcome_P (outcome_add_adjoint_eq_P hr)
      | inr h_y_move =>
          obtain ⟨yr, hyr, rfl⟩ := h_y_move
          change yr ∈ moves .right (rightSeparatorCandidate h x) at hyr
          unfold rightSeparatorCandidate at hyr
          rw [rightMoves_ofSets (s := rightSeparatorLeftSet h) (t := {x})] at hyr
          simp only [Set.mem_singleton_iff] at hyr
          rw [hyr]
          exact hhx

open Classical in
abbrev downlinkZeroLeft (g h : G) : Set G :=
  if IsEnd .right g ∧ IsEnd .right h then {0} else ∅

open Classical in
abbrev downlinkZeroRight (g h : G) : Set G :=
  if IsEnd .left g ∧ IsEnd .left h then {0} else ∅

abbrev downlinkLeftSet (g h : G) (y : moves .right h → G) : Set G :=
  Set.range y ∪ Set.range (fun gr : moves .right g => (gr : G)°) ∪ downlinkZeroLeft g h

abbrev downlinkRightSet (g h : G) (x : moves .left g → G) : Set G :=
  Set.range x ∪ Set.range (fun hl : moves .left h => (hl : G)°) ∪ downlinkZeroRight g h

noncomputable abbrev downlinkWitness
    (g h : G) (x : moves .left g → G) (y : moves .right h → G)
    [Small (downlinkLeftSet g h y)] [Small (downlinkRightSet g h x)] : G :=
  !{downlinkLeftSet g h y | downlinkRightSet g h x}

theorem downlinkLeftSet_nonempty
    (g h : G) (y : moves .right h → G) :
    (downlinkLeftSet g h y).Nonempty := by
  by_cases hz : IsEnd .right g ∧ IsEnd .right h
  · exact ⟨0, by simp [downlinkLeftSet, downlinkZeroLeft, hz]⟩
  · rw [not_and_or] at hz
    cases hz with
    | inl hg =>
        obtain ⟨gr, hgr⟩ := not_IsEnd_exists_move hg
        exact ⟨gr°, by
          simp only [downlinkLeftSet, Set.mem_union, Set.mem_range]
          exact Or.inl (Or.inr ⟨⟨gr, hgr⟩, rfl⟩)⟩
    | inr hh =>
        obtain ⟨hr, hhr⟩ := not_IsEnd_exists_move hh
        exact ⟨y ⟨hr, hhr⟩, by
          simp only [downlinkLeftSet, Set.mem_union, Set.mem_range]
          exact Or.inl (Or.inl ⟨⟨hr, hhr⟩, rfl⟩)⟩

theorem downlinkRightSet_nonempty
    (g h : G) (x : moves .left g → G) :
    (downlinkRightSet g h x).Nonempty := by
  by_cases hz : IsEnd .left g ∧ IsEnd .left h
  · exact ⟨0, by simp [downlinkRightSet, downlinkZeroRight, hz]⟩
  · rw [not_and_or] at hz
    cases hz with
    | inl hg =>
        obtain ⟨gl, hgl⟩ := not_IsEnd_exists_move hg
        exact ⟨x ⟨gl, hgl⟩, by
          simp only [downlinkRightSet, Set.mem_union, Set.mem_range]
          exact Or.inl (Or.inl ⟨⟨gl, hgl⟩, rfl⟩)⟩
    | inr hh =>
        obtain ⟨hl, hhl⟩ := not_IsEnd_exists_move hh
        exact ⟨hl°, by
          simp only [downlinkRightSet, Set.mem_union, Set.mem_range]
          exact Or.inl (Or.inr ⟨⟨hl, hhl⟩, rfl⟩)⟩

theorem downlinked_of_downlinkWitness_mem
    {U : G → Prop} {g h : G}
    {x : moves .left g → G} {y : moves .right h → G}
    [Small (downlinkLeftSet g h y)] [Small (downlinkRightSet g h x)]
    (htU : U (downlinkWitness g h x y))
    (hxLose : ∀ gl : moves .left g, ¬WinsGoingFirst .left ((gl : G) + x gl))
    (hxWin : ∀ gl : moves .left g, WinsGoingFirst .left (h + x gl))
    (hyWin : ∀ hr : moves .right h, WinsGoingFirst .right (g + y hr))
    (hyLose : ∀ hr : moves .right h, ¬WinsGoingFirst .right ((hr : G) + y hr)) :
    Downlinked U g h := by
  let L := downlinkLeftSet g h y
  let R := downlinkRightSet g h x
  let t : G := !{L | R}
  have hLnonempty : L.Nonempty := downlinkLeftSet_nonempty g h y
  have hRnonempty : R.Nonempty := downlinkRightSet_nonempty g h x
  change U t at htU
  refine ⟨t, htU, ?_, ?_⟩
  · rw [not_WinsGoingFirst]
    constructor
    · intro hEnd
      have htEnd : IsEndLike .left t := (IsEndLike.add_iff.mp hEnd).right
      change IsEndLike .left !{L | R} at htEnd
      rw [ofSets_IsEndLike_iff, IsEnd_def, leftMoves_ofSets] at htEnd
      exact hLnonempty.ne_empty htEnd
    · intro k hk
      rw [moves_add] at hk
      rcases hk with ⟨gl, hgl, rfl⟩ | ⟨tl, htl, rfl⟩
      · apply WinsGoingFirst_of_moves
        refine ⟨gl + x ⟨gl, hgl⟩, ?_, hxLose ⟨gl, hgl⟩⟩
        apply add_left_mem_moves_add
        change x ⟨gl, hgl⟩ ∈ moves .right !{L | R}
        rw [rightMoves_ofSets]
        simp [R, downlinkRightSet]
      · change tl ∈ moves .left !{L | R} at htl
        rw [leftMoves_ofSets] at htl
        simp only [L, downlinkLeftSet, downlinkZeroLeft, Set.mem_union, Set.mem_range] at htl
        rcases htl with (⟨hr, htl_eq⟩ | ⟨gr, htl_eq⟩) | htl_zero
        · rw [← htl_eq]
          exact hyWin hr
        · rw [← htl_eq]
          apply WinsGoingFirst_of_moves
          refine ⟨(gr : G) + (gr : G)°, add_right_mem_moves_add gr.2 ((gr : G)°), ?_⟩
          exact not_WinsGoingFirst_of_MisereOutcome_P (outcome_add_adjoint_eq_P (gr : G))
        · by_cases hz : IsEnd .right g ∧ IsEnd .right h
          · simp [hz] at htl_zero
            rw [htl_zero]
            exact WinsGoingFirst_of_IsEndLike
              (IsEndLike.add_iff.mpr ⟨IsEnd.IsEndLike hz.left, IsEnd.IsEndLike IsEnd_zero⟩)
          · simp [hz] at htl_zero
  · rw [not_WinsGoingFirst]
    constructor
    · intro hEnd
      have htEnd : IsEndLike .right t := (IsEndLike.add_iff.mp hEnd).right
      change IsEndLike .right !{L | R} at htEnd
      rw [ofSets_IsEndLike_iff, IsEnd_def, rightMoves_ofSets] at htEnd
      exact hRnonempty.ne_empty htEnd
    · intro k hk
      rw [moves_add] at hk
      rcases hk with ⟨hr, hhr, rfl⟩ | ⟨tr, htr, rfl⟩
      · apply WinsGoingFirst_of_moves
        refine ⟨hr + y ⟨hr, hhr⟩, ?_, hyLose ⟨hr, hhr⟩⟩
        apply add_left_mem_moves_add
        change y ⟨hr, hhr⟩ ∈ moves .left !{L | R}
        rw [leftMoves_ofSets]
        simp [L, downlinkLeftSet]
      · change tr ∈ moves .right !{L | R} at htr
        rw [rightMoves_ofSets] at htr
        simp only [R, downlinkRightSet, downlinkZeroRight, Set.mem_union, Set.mem_range] at htr
        rcases htr with (⟨gl, htr_eq⟩ | ⟨hl, htr_eq⟩) | htr_zero
        · rw [← htr_eq]
          exact hxWin gl
        · rw [← htr_eq]
          apply WinsGoingFirst_of_moves
          refine ⟨(hl : G) + (hl : G)°, add_right_mem_moves_add hl.2 ((hl : G)°), ?_⟩
          exact not_WinsGoingFirst_of_MisereOutcome_P (outcome_add_adjoint_eq_P (hl : G))
        · by_cases hz : IsEnd .left g ∧ IsEnd .left h
          · simp [hz] at htr_zero
            rw [htr_zero]
            exact WinsGoingFirst_of_IsEndLike
              (IsEndLike.add_iff.mpr ⟨IsEnd.IsEndLike hz.right, IsEnd.IsEndLike IsEnd_zero⟩)
          · simp [hz] at htr_zero

end Separation

theorem leftSeparating_neg_of_rightSeparating {U : G → Prop} [ClosedUnderNeg U]
    {g h : G} (h_right_sep : RightSeparating U g h) :
    LeftSeparating U (-h) (-g) := by
  obtain ⟨y, hy, hgy, hhy⟩ := h_right_sep
  refine ⟨-y, ClosedUnderNeg.neg_of hy, ?_, ?_⟩
  · intro h_win
    have h_win' : WinsGoingFirst .right (h + y) := by
      apply (WinsGoingFirst_neg_iff (h + y) .left).mp
      simpa [neg_add_rev, add_comm] using h_win
    exact hhy h_win'
  · have h_win : WinsGoingFirst .left (-(g + y)) :=
      (WinsGoingFirst_neg_iff (g + y) .left).mpr hgy
    simpa [neg_add_rev, add_comm] using h_win

theorem leftSeparating_of_rightSeparating_neg {U : G → Prop} [ClosedUnderNeg U]
    {g h : G} (h_right_sep : RightSeparating U (-h) (-g)) :
    LeftSeparating U g h := by
  obtain ⟨y, hy, hh_y, hg_y⟩ := h_right_sep
  refine ⟨-y, ClosedUnderNeg.neg_of hy, ?_, ?_⟩
  · intro h_win
    have h_win' : WinsGoingFirst .right ((-g) + y) := by
      have h_neg : WinsGoingFirst .right (-(g + (-y))) :=
        (WinsGoingFirst_neg_iff (g + (-y)) .right).mpr h_win
      simpa [neg_add_rev, add_comm] using h_neg
    exact hg_y h_win'
  · apply (WinsGoingFirst_neg_iff (h + (-y)) .right).mp
    simpa [neg_add_rev, add_comm] using hh_y

namespace Separation

class ComparisonSet (A : G → Prop) extends ClosedUnderNeg A where
  legal : G → Prop
  legal_moves {g g' : G} {p : Player} : legal g → g' ∈ moves p g → legal g'
  legal_neg {g : G} : legal g → legal (-g)
  rightSeparatorCandidate_mem {h x : G} :
    legal h → A x → A (rightSeparatorCandidate h x)
  downlinkWitness_mem {g h : G} {x : moves .left g → G} {y : moves .right h → G}
    [Small (downlinkLeftSet g h y)] [Small (downlinkRightSet g h x)] :
    legal g → legal h → (∀ gl, A (x gl)) → (∀ hr, A (y hr)) →
      A (downlinkWitness g h x y)

namespace ComparisonSet

theorem rightSeparating_of_leftSeparating
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hh : legal U h)
    (h_left_sep : LeftSeparating U g h) :
    RightSeparating U g h := by
  refine rightSeparating_of_leftSeparating_of_rightSeparatorCandidate_mem ?_ h_left_sep
  intro x hx
  exact rightSeparatorCandidate_mem hh hx

theorem leftSeparating_of_rightSeparating_of_not_misere_ge
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hg : legal U g)
    (h_not_ge : ¬(g ≥m U h))
    (h_right_sep : RightSeparating U g h) :
    LeftSeparating U g h := by
  have h_not_ge_neg : ¬((-h) ≥m U (-g)) := by
    rwa [ClosedUnderNeg.neg_ge_neg_iff]
  have h_left_sep_neg : LeftSeparating U (-h) (-g) :=
    leftSeparating_neg_of_rightSeparating h_right_sep
  have h_right_sep_neg : RightSeparating U (-h) (-g) :=
    rightSeparating_of_leftSeparating
      (legal_neg hg) h_left_sep_neg
  exact leftSeparating_of_rightSeparating_neg h_right_sep_neg

theorem left_and_right_separating_of_not_misere_ge
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hg : legal U g) (hh : legal U h) (h_not_ge : ¬(g ≥m U h)) :
    LeftSeparating U g h ∧ RightSeparating U g h := by
  cases leftSeparating_or_rightSeparating_of_not_misere_ge h_not_ge with
  | inl h_left =>
      exact ⟨h_left, rightSeparating_of_leftSeparating
        hh h_left⟩
  | inr h_right =>
      exact ⟨leftSeparating_of_rightSeparating_of_not_misere_ge
        hg h_not_ge h_right, h_right⟩

theorem downlinked_of_not_exists_left_right_misere_ge
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hg : legal U g) (hh : legal U h)
    (h_left : ¬∃ gl ∈ moves .left g, gl ≥m U h)
    (h_right : ¬∃ hr ∈ moves .right h, g ≥m U hr) :
    Downlinked U g h := by
  classical
  have h_left_sep :
      ∀ gl : moves .left g, LeftSeparating U (gl : G) h := by
    intro gl
    have h_not_ge : ¬((gl : G) ≥m U h) := by
      intro hge
      exact h_left ⟨gl, gl.2, hge⟩
    exact (left_and_right_separating_of_not_misere_ge
      (legal_moves hg gl.2) hh h_not_ge).left
  have h_right_sep :
      ∀ hr : moves .right h, RightSeparating U g (hr : G) := by
    intro hr
    have h_not_ge : ¬(g ≥m U (hr : G)) := by
      intro hge
      exact h_right ⟨hr, hr.2, hge⟩
    exact (left_and_right_separating_of_not_misere_ge
      hg (legal_moves hh hr.2) h_not_ge).right
  choose x hxU hxLose hxWin using h_left_sep
  choose y hyU hyWin hyLose using h_right_sep
  let L : Set G := downlinkLeftSet g h y
  let R : Set G := downlinkRightSet g h x
  haveI : Small.{u} (downlinkZeroLeft g h) := by
    by_cases hz : IsEnd .right g ∧ IsEnd .right h
    · simpa [downlinkZeroLeft, hz] using (inferInstance : Small.{u} ({0} : Set G))
    · simpa [downlinkZeroLeft, hz] using (inferInstance : Small.{u} (∅ : Set G))
  haveI : Small.{u} (downlinkZeroRight g h) := by
    by_cases hz : IsEnd .left g ∧ IsEnd .left h
    · simpa [downlinkZeroRight, hz] using (inferInstance : Small.{u} ({0} : Set G))
    · simpa [downlinkZeroRight, hz] using (inferInstance : Small.{u} (∅ : Set G))
  haveI : Small.{u} L := inferInstance
  haveI : Small.{u} R := inferInstance
  have htU : U (downlinkWitness g h x y) :=
    downlinkWitness_mem hg hh hxU hyU
  exact downlinked_of_downlinkWitness_mem htU hxLose hxWin hyWin hyLose

theorem misere_ge_imp_maintenance_right
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hg : legal U g) (hh : legal U h) (hge : g ≥m U h) :
    Maintenance U g h .right := by
  intro gr hgr
  by_contra h_not
  have h_downlinked : Downlinked U gr h := by
    apply downlinked_of_not_exists_left_right_misere_ge (legal_moves hg hgr) hh
    · intro h_exists
      exact h_not (Or.inr h_exists)
    · intro h_exists
      exact h_not (Or.inl h_exists)
  obtain ⟨t, ht, hgrt, hht⟩ := h_downlinked
  have hgrt_out : MiserePlayerOutcome (gr + t) .left = .right := by
    unfold MiserePlayerOutcome
    simp [hgrt]
  have hgt : MiserePlayerOutcome (g + t) .right = .right :=
    MiserePlayerOutcome_of_rightMoves (add_right_mem_moves_add hgr t) hgrt_out
  have hht_out : MiserePlayerOutcome (h + t) .right = .left := by
    unfold MiserePlayerOutcome
    simp [hht]
  have h_cmp := MisereOutcome_ge_iff_MiserePlayerOutcome_ge.mp (hge t ht) .right
  rw [hgt, hht_out] at h_cmp
  exact Player.left_le_right h_cmp

theorem misere_ge_imp_maintenance_left
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hg : legal U g) (hh : legal U h) (hge : g ≥m U h) :
    Maintenance U g h .left := by
  intro hl hhl
  by_contra h_not
  have h_downlinked : Downlinked U g hl := by
    apply downlinked_of_not_exists_left_right_misere_ge hg (legal_moves hh hhl)
    · intro h_exists
      exact h_not (Or.inl h_exists)
    · intro h_exists
      exact h_not (Or.inr h_exists)
  obtain ⟨t, ht, hgt, hhlt⟩ := h_downlinked
  have hhlt_out : MiserePlayerOutcome (hl + t) .right = .left := by
    unfold MiserePlayerOutcome
    simp [hhlt]
  have hht : MiserePlayerOutcome (h + t) .left = .left :=
    MiserePlayerOutcome_of_leftMoves (add_right_mem_moves_add hhl t) hhlt_out
  have hgt_out : MiserePlayerOutcome (g + t) .left = .right := by
    unfold MiserePlayerOutcome
    simp [hgt]
  have h_cmp := MisereOutcome_ge_iff_MiserePlayerOutcome_ge.mp (hge t ht) .left
  rw [hgt_out, hht] at h_cmp
  exact Player.left_le_right h_cmp

theorem misere_ge_imp_maintenance_and_proviso
    {U : G → Prop} [ComparisonSet U] {g h : G}
    (hg : legal U g) (hh : legal U h) :
    g ≥m U h →
      Maintenance U g h .right ∧ Maintenance U g h .left ∧
      Proviso U g h .right ∧ Proviso U h g .left := by
  intro hge
  exact ⟨misere_ge_imp_maintenance_right hg hh hge,
    misere_ge_imp_maintenance_left hg hh hge,
    misere_ge_imp_proviso_right hge,
    misere_ge_imp_proviso_left hge⟩

end ComparisonSet

end Separation

end Form
