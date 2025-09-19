import CombinatorialGames.Form
import CombinatorialGames.GameForm
import CombinatorialGames.Misere.Outcome

universe u

def AugmentedFunctor (α : Type (u + 1)) : Type (u + 1) :=
  {s : Player → Set α // ∀ p, Small.{u} (s p)} × (Player → Bool)

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
  P := ⟨(Player → Type u) × (Player → Bool), fun ⟨x, _⟩ ↦ Σ p, PLift (x p)⟩
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

def leftTombstone (x : AugmentedForm.{u}) : Bool := x.dest.2 .left

def rightTombstone (x : AugmentedForm.{u}) : Bool := x.dest.2 .right

def tombstone (p : Player) (x : AugmentedForm.{u}) : Bool := x.dest.2 p

def hasTombstone (p : Player) (x : AugmentedForm) : Prop :=
  x.dest.2 p = True

instance (p : Player) (x : AugmentedForm.{u}) : Small.{u} (x.moves p) := x.dest.1.2 p

def ofSetsWithTombs (st : Player → Set AugmentedForm) (leftTomb rightTomb : Bool)
    [Small.{u} (st .left)] [Small.{u} (st .right)] : AugmentedForm :=
  QPF.Fix.mk ⟨⟨st, fun | .left => inferInstance | .right => inferInstance⟩,
    fun | .left => leftTomb | .right => rightTomb⟩

instance : OfSets AugmentedForm fun _ ↦ True where
  ofSets st _ := ofSetsWithTombs st false false

@[simp]
theorem moves_ofSets (p) (st : Player → Set AugmentedForm) [Small.{u} (st .left)] [Small.{u} (st .right)] :
    !{st}.moves p = st p := by
  dsimp [ofSets, ofSetsWithTombs]; rw [moves, QPF.Fix.dest_mk]

@[simp]
theorem moves_ofSetsWithTombs (p) (st : Player → Set AugmentedForm) (lb rb : Bool)
    [Small.{u} (st .left)] [Small.{u} (st .right)] :
    (ofSetsWithTombs st lb rb).moves p = st p := by
  dsimp [ofSetsWithTombs]; rw [moves, QPF.Fix.dest_mk]

@[simp]
theorem leftTombstone_ofSets (st : Player → Set AugmentedForm) [Small.{u} (st .left)] [Small.{u} (st .right)] :
    !{st}.leftTombstone = false := by
  dsimp [ofSets, ofSetsWithTombs]; rw [leftTombstone, QPF.Fix.dest_mk]

@[simp]
theorem rightTombstone_ofSets (st : Player → Set AugmentedForm) [Small.{u} (st .left)] [Small.{u} (st .right)] :
    !{st}.rightTombstone = false := by
  dsimp [ofSets, ofSetsWithTombs]; rw [rightTombstone, QPF.Fix.dest_mk]

@[simp]
theorem leftTombstone_ofSetsWithTombs (st : Player → Set AugmentedForm) (lb rb : Bool)
    [Small.{u} (st .left)] [Small.{u} (st .right)] :
    (ofSetsWithTombs st lb rb).leftTombstone = lb := by
  dsimp [ofSetsWithTombs]; rw [leftTombstone, QPF.Fix.dest_mk]

@[simp]
theorem rightTombstone_ofSetsWithTombs (st : Player → Set AugmentedForm) (lb rb : Bool)
    [Small.{u} (st .left)] [Small.{u} (st .right)] :
    (ofSetsWithTombs st lb rb).rightTombstone = rb := by
  dsimp [ofSetsWithTombs]; rw [rightTombstone, QPF.Fix.dest_mk]

@[simp]
theorem tombstone_ofSetsWithTombs (p : Player) (st : Player → Set AugmentedForm) (lb rb : Bool)
    [Small.{u} (st .left)] [Small.{u} (st .right)] :
    (ofSetsWithTombs st lb rb).tombstone p = if p = Player.left then lb else rb := by
  cases p with
  | left =>
    rw [tombstone]; dsimp [ofSetsWithTombs]; rw [QPF.Fix.dest_mk]
  | right =>
    rw [tombstone]; dsimp [ofSetsWithTombs]; rw [QPF.Fix.dest_mk]

@[simp]
theorem ofSets_moves_tombs (x : AugmentedForm) :
    ofSetsWithTombs x.moves x.leftTombstone x.rightTombstone = x := by
  simp only [ofSetsWithTombs, moves, Subtype.coe_eta, leftTombstone, rightTombstone]
  unfold AugmentedForm at x
  have h1 : (fun x_1 ↦
        match x_1 with
        | Player.left => x.dest.2 Player.left
        | Player.right => x.dest.2 Player.right) = x.dest.2 := by
       funext p
       cases p <;> rfl
  rw [h1]
  simp only [Prod.mk.eta, QPF.Fix.mk_dest]

@[ext]
theorem ext {x y : AugmentedForm.{u}}
    (h_moves : ∀ p, x.moves p = y.moves p)
    (h_left_tomb : x.leftTombstone = y.leftTombstone)
    (h_right_tomb : x.rightTombstone = y.rightTombstone) :
    x = y := by
  rw [← ofSets_moves_tombs x, ← ofSets_moves_tombs y]
  simp_rw [funext h_moves, h_left_tomb, h_right_tomb]

instance : Form AugmentedForm where
  moves := AugmentedForm.moves
  isOption'_wf := by
    refine ⟨fun x ↦ ?_⟩
    apply QPF.Fix.ind
    unfold Form.IsOption' AugmentedForm.moves
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
noncomputable def EndLike (g : AugmentedForm) (p : Player) : Bool :=
  g.tombstone p || decide (g.moves p = ∅)


private noncomputable def add' (x y : AugmentedForm) : AugmentedForm :=
  ofSetsWithTombs
    (fun p => (Set.range fun z : x.moves p => add' z y) ∪ (Set.range fun z : y.moves p => add' x z))
    ((x.tombstone .left && EndLike y .left) || (y.tombstone .left && EndLike x .left))
    ((x.tombstone .right && EndLike y .right) || (y.tombstone .right && EndLike x .right))
  termination_by (x, y)
  decreasing_by form_wf

noncomputable instance : Add AugmentedForm where
  add := add'

def ofGameForm (g : GameForm) : AugmentedForm :=
  ofSetsWithTombs
    (fun p => Set.range (fun gp : g.moves p => ofGameForm gp))
    false
    false
    termination_by g
    decreasing_by form_wf

instance : Coe GameForm AugmentedForm where
  coe := ofGameForm

def TombstoneFree (g : AugmentedForm) : Prop :=
  ¬g.tombstone .left ∧ ¬g.tombstone .right ∧ ∀ p, ∀ h ∈ g.moves p, TombstoneFree h
  termination_by g
  decreasing_by form_wf

def TombstoneFree.moves {g : AugmentedForm} (h1 : TombstoneFree g) :
  ∀ p, ∀ h ∈ g.moves p, TombstoneFree h := by
  unfold TombstoneFree at h1
  exact h1.right.right

theorem ofSetsWithTombs_ff_TombstoneFree
  {st : Player → Set AugmentedForm} [Small.{u} (st .left)] [Small.{u} (st .right)] (h1 : ∀ p, ∀ gp ∈ st p, TombstoneFree gp) : TombstoneFree (ofSetsWithTombs st false false) := by
  unfold TombstoneFree
  refine ⟨?_, ?_, ?_⟩
  · rw [tombstone_ofSetsWithTombs]
    exact ne_true_of_eq_false rfl
  · rw [tombstone_ofSetsWithTombs]
    exact ne_true_of_eq_false rfl
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
    intro p gp h1
    obtain ⟨h3, h4⟩ := h1
    rw [<-h4]
    exact ih p h3 (Subtype.coe_prop h3)

theorem toGameForm_ofGameForm (g : GameForm) :
  toGameForm (ofGameForm g) (ofGameForm_tombstoneFree g) = g := by
  -- unfold ofGameForm toGameForm
  ext p gp
  constructor <;> intro h1
  · unfold ofGameForm toGameForm at h1
    simp at h1
    cases p
    · simp at h1
      obtain ⟨g2, ⟨g3, ⟨h2, h3⟩⟩, h4⟩ := h1
      simp only [<-h3, <-h4]
      have h5 : ∃ gl, gl ∈ GameForm.moves Player.left g := Exists.intro g3 h2
      obtain ⟨gl, h5⟩ := h5
      -- simp [<-h5]

      sorry
    · sorry
  · sorry

theorem ofGameForm_toGameForm (g : AugmentedForm) (h : TombstoneFree g) :
  ofGameForm (toGameForm g h) = g := by
  sorry

instance : Zero AugmentedForm := ⟨ofSetsWithTombs (fun _ ↦ ∅) false false⟩

theorem zero_def : (0 : AugmentedForm) = ofSetsWithTombs (fun _ ↦ ∅) false false := rfl

@[simp]
theorem moves_zero (p : Player) : (0 : AugmentedForm).moves p = ∅ := by
  rw [zero_def]
  simp [moves_ofSetsWithTombs]
@[simp]

theorem tombstone_zero (p : Player) : (0 : AugmentedForm).tombstone p = false := by
  rw [zero_def, tombstone_ofSetsWithTombs]
  cases p <;> simp

@[simp]
theorem EndLike_zero (p : Player) : EndLike (0 : AugmentedForm) p = true := by
  rw [EndLike, tombstone_zero, Bool.false_or]
  simp [moves_zero]

theorem add_eq (x y : AugmentedForm) : x + y =
    ofSetsWithTombs
      (Player.cases ((· + y) '' xᴸ ∪ (x + ·) '' yᴸ) ((· + y) '' xᴿ ∪ (x + ·) '' yᴿ))
      ((x.tombstone .left && EndLike y .left) || (y.tombstone .left && EndLike x .left))
      ((x.tombstone .right && EndLike y .right) || (y.tombstone .right && EndLike x .right)) := by
  change add' _ _ = _
  rw [add']
  congr 1
  ext p
  cases p <;> simp [HAdd.hAdd, Add.add]

theorem add_eq' (x y : AugmentedForm) : x + y =
    ofSetsWithTombs
      (fun p => (· + y) '' x.moves p ∪ (x + ·) '' y.moves p)
      ((x.tombstone .left && EndLike y .left) || (y.tombstone .left && EndLike x .left))
      ((x.tombstone .right && EndLike y .right) || (y.tombstone .right && EndLike x .right)) := by
  rw [add_eq]
  congr 1
  ext p
  cases p <;> rfl

theorem tombstone_add {x y : AugmentedForm} {p : Player} :
    (x + y).tombstone p = ((x.tombstone p && EndLike y p) || (y.tombstone p && EndLike x p)) := by
  rw [add_eq]
  cases p <;> simp only [tombstone_ofSetsWithTombs, reduceCtorEq, ↓reduceIte]

@[simp]
theorem moves_add (p : Player) (x y : AugmentedForm) :
    (x + y).moves p = (· + y) '' x.moves p ∪ (x + ·) '' y.moves p := by
  rw [add_eq', moves_ofSetsWithTombs]

lemma tombstone_add_zero (g : AugmentedForm) (p : Player) : (g + 0).tombstone p = g.tombstone p := by
  simp only [tombstone_add, EndLike_zero, Bool.and_true, tombstone_zero, Bool.false_and,
             Bool.or_false]

private theorem add_zero' (x : AugmentedForm) : x + 0 = x := by
  refine moveRecOn x ?_
  intro x ih
  ext
  · aesop
  · exact tombstone_add_zero x Player.left
  · exact tombstone_add_zero x Player.right

private theorem add_comm' (x y : AugmentedForm) : x + y = y + x := by
  sorry

private theorem add_assoc' (x y z : AugmentedForm) : x + y + z = x + (y + z) := by
  sorry

noncomputable instance : AddCommMonoid AugmentedForm where
  add_zero := add_zero'
  zero_add x := add_comm' .. ▸ add_zero' x
  add_comm := add_comm'
  add_assoc := add_assoc'
  nsmul := nsmulRec

theorem ofGameForm_zero : ofGameForm (0 : GameForm) = (0 : AugmentedForm) := by
  rw [GameForm.zero_def, zero_def, ofGameForm]
  refine ext ?_ rfl rfl
  intro p
  simp only [moves_ofSetsWithTombs, Set.range_eq_empty_iff, GameForm.moves_ofSets,
             Set.isEmpty_coe_sort]

theorem ofGameForm_moves_mem {g gp : GameForm} {p : Player} (h1 : gp ∈ GameForm.moves p g) :
    ofGameForm gp ∈ moves p (ofGameForm g) := by
  unfold ofGameForm
  rw [moves_ofSetsWithTombs]
  refine Set.mem_range.mpr ?_
  rw [<-ofGameForm]
  refine SetCoe.exists.mpr ?_
  use gp, h1

theorem ofGameForm_add (g h : GameForm) : ofGameForm (g + h) = ofGameForm g + ofGameForm h := by
  rw [add_eq']
  have h1 : (tombstone Player.left (ofGameForm g) && (ofGameForm h).EndLike Player.left ||
        tombstone Player.left (ofGameForm h) && (ofGameForm g).EndLike Player.left) = false := sorry
  have h2 : (tombstone Player.right (ofGameForm g) && (ofGameForm h).EndLike Player.right ||
        tombstone Player.right (ofGameForm h) && (ofGameForm g).EndLike Player.right) = false := sorry
  rw [h1, h2, ofGameForm]
  refine ext ?_ rfl rfl
  intro p
  rw [moves_ofSetsWithTombs, moves_ofSetsWithTombs]
  simp [Set.range_eq_iff]
  constructor
  · intro ghp h3
    apply Or.elim h3 <;> intro h3
    · obtain ⟨gp, h3, h4⟩ := h3
      rw [<-h4]
      apply Or.inl
      use ofGameForm gp
      apply And.intro (ofGameForm_moves_mem h3)
      apply Eq.symm
      exact ofGameForm_add gp h
    · obtain ⟨hp, h3, h4⟩ := h3
      rw [<-h4]
      apply Or.inr
      use ofGameForm hp
      apply And.intro (ofGameForm_moves_mem h3)
      apply Eq.symm
      exact ofGameForm_add g hp
  · intro ghp
    intro h3
    apply Or.elim h3 <;> intro h3
    · obtain ⟨gp, h3, h4⟩ := h3
      rw [<-h4]
      use g
      constructor
      · sorry
      · have h5 : ∃ gpp, gpp ∈ GameForm.moves p g := sorry
        obtain ⟨gpp, h5⟩ := h5
        sorry
    · sorry
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

end AugmentedForm
