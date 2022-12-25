import Playground.Category.Functor.Universal

namespace Category.Construction
section
  open Functor
  variable (C) [Category C]
  namespace Initial
  structure Data where
    object : C
  instance : CoUniversal.CanFactorThrough (Data C) where
    object := Data.object
    FactorsThroughVia _ _ _ := True
    FactorsThroughVia_comp := by simp
    FactorsThroughVia_id := by simp
  end Initial
  structure Initial extends Initial.Data C, CoUniversal.Property toData
end
end Category.Construction