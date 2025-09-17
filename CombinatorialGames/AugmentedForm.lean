import CombinatorialGames.GameForm

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
