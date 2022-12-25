import Playground.Category.Functor.Universal
import Playground.Category.ConcreteCategory

namespace Category.Construction
section
  open Functor

  variable (C) [Concrete C] (S : Type)
  namespace FreeObject
  structure Data where
    object : C
    inclusion : S → toType object
  instance : CoUniversal.CanFactorThrough (Data C S) where
    object := Data.object
    FactorsThroughVia f d α := 
      f.inclusion = d.inclusion ≫ toType.hom_map α
    FactorsThroughVia_comp {f d f' α α'} (hα) (hα') := show _ = _ from
      -- assoc _ α _ ▸ hα ▸ hα'
      sorry
    FactorsThroughVia_id := sorry
  end FreeObject
  structure FreeObject extends FreeObject.Data C S, CoUniversal.Property toData


end
end Category.Construction