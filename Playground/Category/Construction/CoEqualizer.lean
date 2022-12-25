import Playground.Category.Functor.Universal
import Playground.Category.WithZeroMorphisms

namespace Category.Construction
section
  open Functor
  variable {C} [Category C] {X Y : C} (f g : X ⟶ Y)
  namespace CoEqualizer
  structure Data where
    object : C
    morphism : Y ⟶ object
    comm : f ≫ morphism = g ≫ morphism
  instance : CoUniversal.CanFactorThrough (Data f g) where
    object := Data.object
    FactorsThroughVia ψ φ α := φ.morphism ≫ α = ψ.morphism
    FactorsThroughVia_comp {f d f' α α'} (hα : _ = _) (hα' : _ = _) := show _ = _ from
      assoc _ α _ ▸ hα ▸ hα'
    FactorsThroughVia_id := by simp
  end CoEqualizer
  structure CoEqualizer extends CoEqualizer.Data f g, CoUniversal.Property toData
end

section
  open Functor
  variable {C} [Category C] [WithZeroMorphisms C] {X Y : C} (f : X ⟶ Y)
  namespace CoKernel
  structure Data where
    object : C
    morphism : Y ⟶ object
    comm : f ≫ morphism = 𝟬 _ _
  instance : CoUniversal.CanFactorThrough (Data f) where
    object := Data.object
    FactorsThroughVia ψ φ α := φ.morphism ≫ α = ψ.morphism
    FactorsThroughVia_comp {f d f' α α'} (hα : _ = _) (hα' : _ = _) := show _ = _ from
      assoc _ α _ ▸ hα ▸ hα'
    FactorsThroughVia_id := by simp
  end CoKernel
  structure CoKernel extends CoKernel.Data f, CoUniversal.Property toData
end

section
  open Functor
  universe u
  variable {X : Type u} (s : Setoid X)
  namespace Quotient
  structure Data.{v} where
    object : Type v
    morphism : X → object
    sound : ∀ x y : X, x ≈ y → morphism x = morphism y
  instance : CoUniversal.CanFactorThrough (Data s) where
    object := Data.object
    FactorsThroughVia f π f' := π.morphism ≫ f' = f.morphism
    FactorsThroughVia_comp {f d f' α α'} (hα : _ = _) (hα' : _ = _) := show _ = _ from
      assoc _ α _ ▸ hα ▸ hα'
    FactorsThroughVia_id g := by simp
  end Quotient
  structure Quotient extends Quotient.Data s, CoUniversal.Property toData

  noncomputable def isomorphismOfSolutions (h : Quotient s) (h' : Quotient s) : h.object ≅ h'.object :=
    let this : (d : Quotient s) → CoUniversal.Property d.toData := Quotient.toProperty
    CoUniversal.isomorphismOfSolutions h.toData h'.toData
end
end Category.Construction
namespace Category
example {X} (s : Setoid X) : Construction.Quotient s where
  object := Quotient s
  morphism := Quotient.mk s
  sound _ _ := Quotient.sound
  existence
  | { object := Y
      morphism := f
      sound := h } =>
    ⟨show Quotient s → Y from Quotient.lift f h, 
    show (Quotient.lift f h) ∘ (Quotient.mk s) = f from funext λ _ => rfl⟩
  uniqueness
  | { object := Y,
      morphism := f,
      sound := h },
    (α : Quotient s → Y), (β : Quotient s → Y),
    (hα : α ∘ (Quotient.mk s) = f), (hβ : β ∘ (Quotient.mk s) = f) =>
      have : α ∘ (Quotient.mk s) = β ∘ (Quotient.mk s) := hα ▸ hβ ▸ rfl
      funext <| Quotient.ind <| congrFun <| this
end Category