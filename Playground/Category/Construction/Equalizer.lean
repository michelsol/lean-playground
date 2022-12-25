import Playground.Category.Functor.Universal
import Playground.Category.WithZeroMorphisms

namespace Category.Construction
section
  open Functor
  variable {C} [Category C] {X Y : C} (f g : X ⟶ Y)
  namespace Equalizer
  structure Data where
    object : C
    morphism : object ⟶ X
    comm : morphism ≫ f = morphism ≫ g
  instance : Universal.CanFactorThrough (Data f g) where
    object := Data.object
    FactorsThroughVia ψ φ α := α ≫ φ.morphism = ψ.morphism
    FactorsThroughVia_comp {f d f' α α'} (hα : _ = _) (hα' : _ = _) := show _ = _ from
      assoc _ α _ ▸ hα ▸ hα'
    FactorsThroughVia_id := by simp
  end Equalizer
  structure Equalizer extends Equalizer.Data f g, Universal.Property toData
end

section
  open Functor
  variable {C} [Category C] [WithZeroMorphisms C] {X Y : C} (f : X ⟶ Y)
  namespace Kernel
  structure Data where
    object : C
    morphism : object ⟶ X
    comm : morphism ≫ f = 𝟬 _ _
  instance : Universal.CanFactorThrough (Data f) where
    object := Data.object
    FactorsThroughVia ψ φ α := α ≫ φ.morphism = ψ.morphism
    FactorsThroughVia_comp {f d f' α α'} (hα : _ = _) (hα' : _ = _) := show _ = _ from
      assoc _ α _ ▸ hα ▸ hα'
    FactorsThroughVia_id := by simp
  end Kernel
  structure Kernel extends Kernel.Data f, Universal.Property toData
end
end Category.Construction