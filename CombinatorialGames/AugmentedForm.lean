import CombinatorialGames.Form
import CombinatorialGames.GameForm
import CombinatorialGames.Misere.Outcome

universe u

def AugmentedFunctor (α : Type (u + 1)) : Type (u + 1) :=
  {s : Player → Set α // ∀ p, Small.{u} (s p)} × (Player → Prop)

namespace AugmentedFunctor

@[ext] theorem ext {α : Type (u + 1)} {x y : AugmentedFunctor α} : x.1 = y.1 → x.2 = y.2 → x = y := by
  intro h1 h2
  apply Prod.ext
  · exact h1
  · exact h2

instance {α : Type (u + 1)} (x : AugmentedFunctor α) (p : Player) : Small.{u} (x.1.1 p) := x.1.2 p

instance : Functor AugmentedFunctor where
  map f s := ⟨⟨(f '' s.1.1 ·), fun _ => inferInstance⟩, s.2⟩

theorem map_def {α β} (f : α → β) (s : AugmentedFunctor α) :
    f <$> s = ⟨⟨(f '' s.1.1 ·), fun _ => inferInstance⟩, s.2⟩ :=
  rfl

instance : QPF AugmentedFunctor where
  P := ⟨(Player → Type u) × (Player → Prop), fun ⟨x, _⟩ ↦ Σ p, PLift (x p)⟩
  abs x := ⟨⟨fun p ↦ Set.range (x.2 ∘ .mk p ∘ PLift.up), fun _ ↦ inferInstance⟩, x.1.2⟩
  repr x := ⟨⟨fun p ↦ Shrink (x.1.1 p), x.2⟩, Sigma.rec (fun _ y ↦ ((equivShrink _).symm y.1).1)⟩
  abs_repr x := by
    cases x with | mk s b =>
    ext; simp [← (equivShrink _).exists_congr_right]; simp
  abs_map f := by
    intro ⟨⟨x, b⟩, g⟩
    ext; simp [PFunctor.map, map_def]
    · simp; rfl

end AugmentedFunctor

def AugmentedForm : Type (u + 1) :=
  QPF.Fix AugmentedFunctor

namespace AugmentedForm

def moves (p : Player) (x : AugmentedForm.{u}) : Set AugmentedForm.{u} :=
  x.dest.1.1 p

scoped notation:max x:max "ᴸ" => moves Player.left x

scoped notation:max x:max "ᴿ" => moves Player.right x

def hasTombstone (p : Player) (x : AugmentedForm) : Prop :=
  x.dest.2 p

instance (p : Player) (x : AugmentedForm.{u}) : Small.{u} (x.moves p) := x.dest.1.2 p

def ofSetsWithTombs (st : Player → Set AugmentedForm) (tomb : Player → Prop)
    [Small.{u} (st .left)] [Small.{u} (st .right)] : AugmentedForm :=
  QPF.Fix.mk ⟨⟨st, fun | .left => inferInstance | .right => inferInstance⟩, tomb⟩

instance : OfSets AugmentedForm fun _ ↦ True where
  ofSets st _ := ofSetsWithTombs st (fun _ => False)

@[simp]
theorem moves_ofSets (p) (st : Player → Set AugmentedForm) [Small.{u} (st .left)] [Small.{u} (st .right)] :
    !{st}.moves p = st p := by
  dsimp [ofSets, ofSetsWithTombs]; rw [moves, QPF.Fix.dest_mk]

@[simp]
theorem moves_ofSetsWithTombs (p) (st : Player → Set AugmentedForm) (tomb : Player → Prop)
    [Small.{u} (st .left)] [Small.{u} (st .right)] :
    (ofSetsWithTombs st tomb).moves p = st p := by
  dsimp [ofSetsWithTombs]; rw [moves, QPF.Fix.dest_mk]

@[simp]
theorem hasTombstone_ofSets
    (st : Player → Set AugmentedForm) [Small.{u} (st .left)] [Small.{u} (st .right)]
    (p : Player): ¬!{st}.hasTombstone p := by
  dsimp [ofSets, ofSetsWithTombs]
  rw [hasTombstone, QPF.Fix.dest_mk]
  cases p <;> simp only [not_false_eq_true]

@[simp]
theorem hasTombstone_ofSetsWithTombs (p : Player) (st : Player → Set AugmentedForm)
    [Small.{u} (st .left)] [Small.{u} (st .right)] (tomb : Player → Prop)
    : (ofSetsWithTombs st tomb).hasTombstone p = tomb p := by
  simp only [hasTombstone, ofSetsWithTombs, QPF.Fix.dest_mk]

@[simp]
theorem ofSets_moves_tombs (x : AugmentedForm) :
    ofSetsWithTombs x.moves (fun p => x.hasTombstone p) = x := by
  simp only [ofSetsWithTombs, moves, Subtype.coe_eta, hasTombstone]
  unfold AugmentedForm at x
  have h1 : (fun x_1 ↦
        match x_1 with
        | Player.left => x.dest.2 Player.left
        | Player.right => x.dest.2 Player.right) = x.dest.2 := by
       funext p
       cases p <;> rfl
  simp only [Prod.mk.eta, QPF.Fix.mk_dest]

@[ext]
theorem ext {x y : AugmentedForm.{u}}
    (h_moves : ∀ p, x.moves p = y.moves p)
    (h_tomb : ∀ p, x.hasTombstone p ↔ y.hasTombstone p)
    : x = y := by
  rw [← ofSets_moves_tombs x, ← ofSets_moves_tombs y]
  simp_rw [funext h_moves, h_tomb]

instance : Moves AugmentedForm where
  moves := AugmentedForm.moves
  isOption'_wf := by
    refine ⟨fun x ↦ ?_⟩
    apply QPF.Fix.ind
    unfold Moves.IsOption' AugmentedForm.moves
    rintro _ ⟨⟨st, hst⟩, rfl⟩
    constructor
    rintro y hy
    rw [QPF.Fix.dest_mk, Set.mem_iUnion] at hy
    obtain ⟨_, ⟨_, h⟩, _, rfl⟩ := hy
    exact h

-- We make no use of `AugmentedForm`'s definition from a `QPF` after this point.

attribute [irreducible] AugmentedForm

@[elab_as_elim]
def moveRecOn {motive : AugmentedForm → Sort*} (x)
    (mk : Π x, (Π p, Π y ∈ x.moves p, motive y) → motive x) : motive x :=
  mk x (fun p y _ ↦ moveRecOn y mk)
  termination_by x
  decreasing_by form_wf

theorem moveRecOn_eq {motive : AugmentedForm → Sort*} (x)
    (mk : Π x, (Π p, Π y ∈ x.moves p, motive y) → motive x) :
    moveRecOn x mk = mk x (fun _ y _ ↦ moveRecOn y mk) := by
  rw [moveRecOn]

def WinsGoingFirst (p : Player) (g : AugmentedForm) : Prop :=
  g.hasTombstone p ∨ g.moves p = ∅ ∨ (∃ g', ∃ (_ : g' ∈ g.moves p), ¬WinsGoingFirst (-p) g')
  termination_by g
  decreasing_by form_wf

instance : MisereForm AugmentedForm where
  WinsGoingFirst := AugmentedForm.WinsGoingFirst

open scoped Classical in
noncomputable def EndLike (g : AugmentedForm) (p : Player) : Prop :=
  g.hasTombstone p ∨ (g.moves p = ∅) -- TODO: .IsEnd to be form-polymorphic


private noncomputable def add' (x y : AugmentedForm) : AugmentedForm :=
  ofSetsWithTombs
    (fun p => (Set.range fun z : x.moves p => add' z y) ∪ (Set.range fun z : y.moves p => add' x z))
    (fun p => (x.hasTombstone p ∧ EndLike y p) ∨ (y.hasTombstone p ∧ EndLike x p))
  termination_by (x, y)
  decreasing_by form_wf

noncomputable instance : Add AugmentedForm where
  add := add'

def ofGameForm (g : GameForm) : AugmentedForm :=
  ofSetsWithTombs
    (fun p => Set.range (fun gp : g.moves p => ofGameForm gp))
    (fun _ => False)
    termination_by g
    decreasing_by form_wf

instance : Coe GameForm AugmentedForm where
  coe := ofGameForm

def TombstoneFree (g : AugmentedForm) : Prop :=
  (∀ p, ¬g.hasTombstone p) ∧ ∀ p, ∀ h ∈ g.moves p, TombstoneFree h
  termination_by g
  decreasing_by form_wf

def TombstoneFree.not_hasTombstone {g : AugmentedForm} (h1 : TombstoneFree g) :
  ∀ p, ¬g.hasTombstone p := by
  unfold TombstoneFree at h1
  exact h1.left

def TombstoneFree.moves {g : AugmentedForm} (h1 : TombstoneFree g) :
  ∀ p, ∀ h ∈ g.moves p, TombstoneFree h := by
  unfold TombstoneFree at h1
  exact h1.right

theorem ofSetsWithTombs_ff_TombstoneFree
    {st : Player → Set AugmentedForm} [Small.{u} (st .left)] [Small.{u} (st .right)]
    (h1 : ∀ p, ∀ gp ∈ st p, TombstoneFree gp) : TombstoneFree (ofSetsWithTombs st (fun _ => False)) := by
  unfold TombstoneFree
  constructor
  · simp only [hasTombstone_ofSetsWithTombs, forall_const, not_false_eq_true]
  · intro p gp h2
    refine h1 p gp ?_
    rw [moves_ofSetsWithTombs] at h2
    exact h2

def toGameForm (g : AugmentedForm) (h : TombstoneFree g) : GameForm :=
  !{Set.range (fun gl : gᴸ => toGameForm gl (h.moves .left gl gl.property)) |
    Set.range (fun gr : gᴿ => toGameForm gr (h.moves .right gr gr.property))}
termination_by g
decreasing_by form_wf

theorem ofGameForm_tombstoneFree (g : GameForm) : TombstoneFree (ofGameForm g) := by
  induction g using GameForm.moveRecOn with
  | mk g ih =>
    unfold ofGameForm
    apply ofSetsWithTombs_ff_TombstoneFree
    intro p gp ⟨h3, h4⟩
    rw [<-h4]
    exact ih p h3 (Subtype.coe_prop h3)

theorem not_hasTombstone_ofGameForm (g : GameForm) (p : Player)
    : ¬hasTombstone p (ofGameForm g) :=
  (ofGameForm_tombstoneFree g).not_hasTombstone p

theorem ofSetsWithTombs_eq
    {as : Player → Set AugmentedForm} [Small.{u} (as .left)] [Small.{u} (as .right)]
    {bs : Player → Set AugmentedForm} [Small.{u} (bs .left)] [Small.{u} (bs .right)]
    {tombL tombR : Player → Prop}
    (h1 : ofSetsWithTombs as tombL = ofSetsWithTombs bs tombR) : as = bs := by
  have ⟨h2, _⟩ := AugmentedForm.ext_iff.mp h1
  simp only [moves_ofSetsWithTombs] at h2
  exact funext_iff.mpr h2

private theorem ofGameForm_Injective' {x y : GameForm} (h1 : ofGameForm x = ofGameForm y)
    : x = y := by
  ext p g
  have h3 := (fun p => congrArg (moves p) h1) p
  unfold ofGameForm at h3
  simp only [moves_ofSetsWithTombs, Set.range_eq_iff, Set.mem_range, Subtype.exists, exists_prop,
             Subtype.forall, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h3
  obtain ⟨h3, h4⟩ := h3
  constructor <;> intro h5
  · obtain ⟨yp, h6, h7⟩ := h3 g h5
    rw [ofGameForm_Injective' h7.symm]
    exact h6
  · obtain ⟨xp, h6, h7⟩ := h4 g h5
    rw [(ofGameForm_Injective' h7).symm]
    exact h6
termination_by (x, y)
decreasing_by form_wf

theorem ofGameForm_Injective : Function.Injective ofGameForm := by
  intro _ _ h1
  exact ofGameForm_Injective' h1

theorem ofGameForm_moves_mem_iff {g gp : GameForm} {p : Player}
    : (ofGameForm gp ∈ moves p (ofGameForm g)) ↔ (gp ∈ GameForm.moves p g) := by
  constructor <;> intro h1
  · rw [ofGameForm, moves_ofSetsWithTombs] at h1
    simp only [Set.mem_range, Subtype.exists, exists_prop] at h1
    obtain ⟨gpp, h1, h2⟩ := h1
    have h3 : gpp = gp := ofGameForm_Injective h2
    rw [<-h3]
    exact h1
  · unfold ofGameForm
    rw [moves_ofSetsWithTombs]
    refine Set.mem_range.mpr ?_
    rw [<-ofGameForm]
    refine SetCoe.exists.mpr ?_
    use gp, h1

theorem toGameForm_moves_mem' {g gp : AugmentedForm} {p : Player} (h1 : gp ∈ moves p g)
    (h2 : TombstoneFree g)
    : (toGameForm gp (TombstoneFree.moves h2 p gp h1) ∈ GameForm.moves p (toGameForm g h2)) := by
  unfold toGameForm
  cases p
  all_goals
  · simp only [GameForm.moves_ofSets, Set.mem_range, Subtype.exists]
    use gp, h1
    rw [toGameForm]

@[simp]
theorem toGameForm_ofGameForm (g : GameForm) :
  toGameForm (ofGameForm g) (ofGameForm_tombstoneFree g) = g := by
  ext p gp
  constructor <;> intro h1
  · unfold ofGameForm toGameForm at h1
    simp only [GameForm.moves_ofSets, Player.cases] at h1
    cases p
    all_goals
    · simp only [Set.mem_range, Subtype.exists, moves_ofSetsWithTombs, exists_prop] at h1
      obtain ⟨g2, ⟨g3, ⟨h2, h3⟩⟩, h4⟩ := h1
      simp only [<-h3, <-h4, toGameForm_ofGameForm g3]
      exact h2
  · unfold ofGameForm toGameForm
    simp only [GameForm.moves_ofSets, Player.cases]
    cases p
    all_goals
    · simp only [Set.mem_range, Subtype.exists, moves_ofSetsWithTombs, exists_prop]
      use (ofGameForm gp)
      exact Exists.intro (by use gp) (toGameForm_ofGameForm gp)
termination_by g
decreasing_by form_wf

@[simp]
theorem ofGameForm_toGameForm (g : AugmentedForm) (h1 : TombstoneFree g) :
  ofGameForm (toGameForm g h1) = g := by
  unfold ofGameForm
  ext p x
  · simp only [moves_ofSetsWithTombs, Set.mem_range, Subtype.exists, exists_prop]
    constructor <;> intro h2
    · unfold toGameForm ofGameForm at h2
      simp only [GameForm.moves_ofSets, Player.cases] at h2
      cases p
      all_goals
      · simp only [Set.mem_range, Subtype.exists] at h2
        obtain ⟨gg, ⟨gl, h3, h4⟩, h5⟩ := h2
        rw [<-h5, <-ofGameForm, <-h4, ofGameForm_toGameForm gl (TombstoneFree.moves h1 _ gl h3)]
        exact h3
    · use toGameForm x (TombstoneFree.moves h1 p x h2)
      constructor
      · exact toGameForm_moves_mem' h2 h1
      · exact ofGameForm_toGameForm x (TombstoneFree.moves h1 p x h2)
  · simp only [hasTombstone_ofSetsWithTombs, h1, TombstoneFree.not_hasTombstone]
termination_by g
decreasing_by form_wf

instance : Zero AugmentedForm := ⟨ofSetsWithTombs (fun _ ↦ ∅) (fun _ => False)⟩

theorem zero_def : (0 : AugmentedForm) = ofSetsWithTombs (fun _ ↦ ∅) (fun _ => False) := rfl

@[simp]
theorem moves_zero (p : Player) : (0 : AugmentedForm).moves p = ∅ := by
  rw [zero_def]
  simp only [moves_ofSetsWithTombs]

@[simp]
theorem not_hasTombstone_zero (p : Player) : ¬(0 : AugmentedForm).hasTombstone p := by
  rw [zero_def, hasTombstone_ofSetsWithTombs]
  cases p <;> simp only [not_false_eq_true]

@[simp]
theorem EndLike_zero (p : Player) : EndLike (0 : AugmentedForm) p := by
  simp only [EndLike, not_hasTombstone_zero, moves_zero, or_true]

theorem add_eq (x y : AugmentedForm) : x + y =
    ofSetsWithTombs
      (Player.cases ((· + y) '' xᴸ ∪ (x + ·) '' yᴸ) ((· + y) '' xᴿ ∪ (x + ·) '' yᴿ))
      (Player.cases
        ((x.hasTombstone .left ∧ EndLike y .left) ∨ (y.hasTombstone .left ∧ EndLike x .left))
        ((x.hasTombstone .right ∧ EndLike y .right) ∨ (y.hasTombstone .right ∧ EndLike x .right))) := by
  change add' _ _ = _
  rw [add']
  congr 1
  all_goals
  · ext p
    cases p <;> simp [HAdd.hAdd, Add.add]

theorem add_eq' (x y : AugmentedForm) : x + y =
    ofSetsWithTombs
      (fun p => (· + y) '' x.moves p ∪ (x + ·) '' y.moves p)
      (fun p => (x.hasTombstone p ∧ EndLike y p) ∨ (y.hasTombstone p ∧ EndLike x p)) := by
  rw [add_eq]
  congr 1
  all_goals
  · ext p
    cases p <;> rfl

theorem hasTombstone_add {x y : AugmentedForm} {p : Player} :
    (x + y).hasTombstone p ↔ ((x.hasTombstone p ∧ EndLike y p) ∨ (y.hasTombstone p ∧ EndLike x p)) := by
  rw [add_eq]
  cases p <;> simp only [hasTombstone_ofSetsWithTombs]

@[simp]
private theorem moves_add' (p : Player) (x y : AugmentedForm) :
    (x + y).moves p = (· + y) '' x.moves p ∪ (x + ·) '' y.moves p := by
  rw [add_eq', moves_ofSetsWithTombs]

lemma hasTombstone_add_zero (g : AugmentedForm) (p : Player)
    : (g + 0).hasTombstone p ↔ g.hasTombstone p := by
  simp only [hasTombstone_add, EndLike_zero, and_true, not_hasTombstone_zero, false_and, or_false]

private theorem add_zero' (x : AugmentedForm) : x + 0 = x := by
  refine moveRecOn x ?_
  intro x ih
  ext
  · aesop
  · exact hasTombstone_add_zero x _

private theorem add_comm' (x y : AugmentedForm) : x + y = y + x := by
  ext
  · simp only [moves_add', Set.mem_union, Set.mem_image, or_comm]
    congr! 3 <;>
    · refine and_congr_right_iff.2 fun h ↦ ?_
      rw [add_comm']
  · simp only [hasTombstone_add, and_comm, or_comm]
termination_by (x, y)
decreasing_by form_wf

private lemma hasTombstone_add_assoc (x y z : AugmentedForm) (p : Player) :
    hasTombstone p (x + y + z) ↔ hasTombstone p (x + (y + z)) := by
  simp only [hasTombstone_add]
  unfold EndLike
  by_cases h1 : hasTombstone p x
  <;> by_cases h2 : hasTombstone p y
  <;> by_cases h3 : hasTombstone p z
  <;> simp only [h1, h2, h3, hasTombstone_add, And.comm, EndLike, Set.image_eq_empty,
                 Set.union_empty_iff, and_imp, and_self, and_true, false_and, false_or,
                 iff_or_self, moves_add', or_false, or_iff_left_iff_imp, or_self, or_self_left,
                 true_and, true_or]
  <;> by_cases h4 : moves p x = ∅
  <;> by_cases h5 : moves p y = ∅
  <;> by_cases h6 : moves p z = ∅
  <;> simp only [h4, h5, h6, and_true, and_false, or_false, or_self,
                 implies_true, imp_self, imp_false, not_true_eq_false]

private theorem add_assoc' (x y z : AugmentedForm) : x + y + z = x + (y + z) := by
  ext1
  · simp only [moves_add', Set.image_union, Set.image_image, Set.union_assoc]
    refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_) <;>
    · ext
      congr! 2
      rw [add_assoc']
  · exact hasTombstone_add_assoc x y z _
termination_by (x, y, z)
decreasing_by form_wf

noncomputable instance : AddCommMonoid AugmentedForm where
  add_zero := add_zero'
  zero_add x := add_comm' .. ▸ add_zero' x
  add_comm := add_comm'
  add_assoc := add_assoc'
  nsmul := nsmulRec

theorem ofGameForm_zero : ofGameForm (0 : GameForm) = (0 : AugmentedForm) := by
  rw [GameForm.zero_def, zero_def, ofGameForm]
  refine ext ?_ ?_
  · intro p
    simp only [moves_ofSetsWithTombs, Set.range_eq_empty_iff, GameForm.moves_ofSets,
               Set.isEmpty_coe_sort]
  · simp only [hasTombstone_ofSetsWithTombs, implies_true]

theorem ofGameForm_exists_preimage {a : AugmentedForm} (h1 : TombstoneFree a)
    : ∃g, ofGameForm g = a := by
  unfold ofGameForm
  use !{fun p => Set.range (fun ap : moves p a => toGameForm ap (h1.moves p ap (Subtype.coe_prop ap)))}
  refine AugmentedForm.ext_iff.mpr ?_
  simp only [moves_ofSetsWithTombs]
  constructor
  · intro p
    refine Eq.symm (Set.ext ?_)
    intro al
    constructor <;> intro h2
    · simp only [Set.mem_range, Subtype.exists, GameForm.moves_ofSets, exists_prop]
      use (toGameForm al (TombstoneFree.moves h1 p al h2))
      simp only [ofGameForm_toGameForm, and_true]
      use al, h2
    · simp only [Set.mem_range, Subtype.exists, GameForm.moves_ofSets, exists_prop] at h2
      obtain ⟨g1, ⟨g2, h6, h7⟩, h5⟩ := h2
      simp only [<-h5, <-h7, ofGameForm_toGameForm, h6]
  · simp only [h1, hasTombstone_ofSetsWithTombs, TombstoneFree.not_hasTombstone, implies_true]

theorem mem_moves_ofGameForm {g : GameForm} {ap : AugmentedForm} {p : Player}
    (h1 : ap ∈ moves p (ofGameForm g)): ∃gp ∈ GameForm.moves p g, ofGameForm gp = ap := by
  have h2 : TombstoneFree (ofGameForm g) := by exact ofGameForm_tombstoneFree g
  have h3 : TombstoneFree ap := TombstoneFree.moves h2 p ap h1
  obtain ⟨gp, h3⟩ := ofGameForm_exists_preimage h3
  use gp
  refine And.intro ?_ h3
  rw [<-h3] at h1
  exact ofGameForm_moves_mem_iff.mp h1

theorem ofGameForm_add (g h : GameForm) : ofGameForm (g + h) = ofGameForm g + ofGameForm h := by
  rw [add_eq']
  simp only [not_hasTombstone_ofGameForm, false_and, or_self]
  rw [GameForm.add_eq']
  rw [ofGameForm]
  refine ext ?_ (by simp only [hasTombstone_ofSetsWithTombs, implies_true])
  intro p
  simp only [moves_ofSetsWithTombs, Set.range_eq_iff, Set.mem_union, Set.mem_image, Subtype.forall,
             GameForm.moves_ofSets, Subtype.exists, exists_prop]
  constructor
  · intro ghp h3
    apply Or.elim h3 <;> intro ⟨x, h3, h4⟩ <;> rw [<-h4]
    · apply Or.inl
      use ofGameForm x
      exact And.intro (ofGameForm_moves_mem_iff.mpr h3) (ofGameForm_add x h).symm
    · apply Or.inr
      use ofGameForm x
      exact And.intro (ofGameForm_moves_mem_iff.mpr h3) (ofGameForm_add g x).symm
  · intro ghp h3
    apply Or.elim h3
      <;> intro ⟨_, h3, h4⟩
      <;> obtain ⟨x, h5, h6⟩ := mem_moves_ofGameForm h3
      <;> rw [<-h4]
    · use (x + h)
      constructor
      · apply Or.inl
        use x
      · rw [<-h6]
        exact ofGameForm_add x h
    · use (g + x)
      constructor
      · apply Or.inr
        use x
      · rw [<-h6]
        exact ofGameForm_add g x
termination_by (g, h)
decreasing_by form_wf

/-- The coercion from GameForm to AugmentedForm is an additive monoid homomorphism -/
def ofGameFormHom : GameForm →+ AugmentedForm where
  toFun := ofGameForm
  map_zero' := ofGameForm_zero
  map_add' := ofGameForm_add

theorem ofGameFormHom_injective : Function.Injective ofGameFormHom := by
  intro g h eq
  rw [← toGameForm_ofGameForm g, ← toGameForm_ofGameForm h]
  congr 1

private def neg' (x : AugmentedForm) : AugmentedForm :=
  ofSetsWithTombs
    (fun p => (Set.range fun xp : x.moves (-p) => neg' xp))
    (fun p => hasTombstone (-p) x)
termination_by x
decreasing_by form_wf

instance : Neg AugmentedForm where
  neg := neg'

theorem neg_eq (x : AugmentedForm)
    : (-x) = ofSetsWithTombs
               (fun p => (Set.range fun xp : x.moves (-p) => -xp))
               (fun p => hasTombstone (-p) x) := by
  simp only [Neg.neg, Player.cases]
  rw [neg']
  congr

private theorem neg_eq' (x : AugmentedForm)
    : (-x) = ofSetsWithTombs
               (fun p => (Set.range fun xp : x.moves (-p) => neg' xp))
               (fun p => hasTombstone (-p) x) := by
  simp only [Neg.neg, Player.cases]
  rw [neg']
  congr

private theorem neg'_eq (x : AugmentedForm) : (-x) = neg' x := by rfl

private theorem neg_neg' (x : AugmentedForm) : -(-x) = x := by
  simp only [neg_eq', hasTombstone_ofSetsWithTombs, neg_neg]
  rw [<-ofSets_moves_tombs x]
  congr
  funext p
  ext xp
  simp only [Set.mem_range, Subtype.exists, ofSets_moves_tombs, moves_ofSetsWithTombs,
             exists_prop, exists_exists_and_eq_and]
  constructor <;> intro h1
  · obtain ⟨yp, h1, h2⟩ := h1
    have h3 : neg' (neg' yp) = -(-yp) := rfl
    rw [<-h2, h3, neg_neg' yp]
    rw [neg_neg] at h1
    exact h1
  · use xp
    rw [neg_neg p]
    apply And.intro h1
    have h3 : neg' (neg' xp) = -(-xp) := rfl
    rw [h3, neg_neg' xp]
termination_by x
decreasing_by form_wf

instance : InvolutiveNeg AugmentedForm where
  neg_neg := neg_neg'

@[simp]
noncomputable instance : Form AugmentedForm where
  moves_neg := by
    intro p x
    simp only [neg_eq']
    simp only [Form.moves, ←neg'_eq, ←Set.neg_range, Subtype.range_coe_subtype, Set.setOf_mem_eq,
               moves_ofSetsWithTombs]
  moves_add := moves_add'

end AugmentedForm
