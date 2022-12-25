import Playground.Category.Functor.Universal

namespace Category.Construction
section
  open Functor
  variable (C) [Category C]
  namespace Terminal
  structure Data where
    object : C
  instance : Universal.CanFactorThrough (Data C) where
    object := Data.object
    FactorsThroughVia _ _ _ := True
    FactorsThroughVia_comp := by simp
    FactorsThroughVia_id := by simp
  end Terminal
  structure Terminal extends Terminal.Data C, Universal.Property toData
end
section
  class Terminals (C) [Category C] where
    terminal : Terminal C
  export Terminals (terminal)
end
end Category.Construction