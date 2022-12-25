import Playground.Category.Functor.Universal

namespace Category.Construction
section
  open Functor
  variable (C) [Category C]
  namespace ZeroObject
  structure Data where
    object : C
  instance : Universal.CanFactorThrough (Data C) where
    object := Data.object
    FactorsThroughVia _ _ _ := True
    FactorsThroughVia_comp := by simp
    FactorsThroughVia_id := by simp
  instance : CoUniversal.CanFactorThrough (Data C) where
    object := Data.object
    FactorsThroughVia _ _ _ := True
    FactorsThroughVia_comp := by simp
    FactorsThroughVia_id := by simp
  end ZeroObject
  structure ZeroObject extends ZeroObject.Data C where
    initial : CoUniversal.Property toData
    terminal : Universal.Property toData
end
end Category.Construction