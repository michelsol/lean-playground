import Playground.Category.Basic
import Playground.Category.Construction.BinaryProduct
import Playground.Category.Construction.Product
import Playground.Category.Construction.Pullback

namespace Category.Internal

section
  open Construction

  abbrev AmbientCategory := Category

  -- define an internal category in some ambient category V
  structure Category (V) [AmbientCategory V] [Pullbacks V] where
    obj : V
    hom : V
    source : hom ⟶ obj
    target : hom ⟶ obj
    id : obj ⟶ hom
    comp : (pullbackOf target source).object ⟶ hom -- { f, g // t(f) = s(g) } → hom
    source_of_id : id ≫ source = 𝟙 obj -- this expresses the commutativity of a diagram


  structure CommMagma (V) [AmbientCategory V] [BinaryProducts V] where
    G : V
    op : (binaryProductOf G G).object ⟶ G
    comm : 
      let GxG := binaryProductOf G G
      let xyToxy : GxG.object ⟶ GxG.object := (GxG.existence {
        morphism₁ := GxG.morphism₁
        morphism₂ := GxG.morphism₂
      }).choose
      let xyToyx : GxG.object ⟶ GxG.object := (GxG.existence {
        morphism₁ := GxG.morphism₂
        morphism₂ := GxG.morphism₁
      }).choose
      xyToxy = xyToyx -- this expresses the commutativity of a diagram


end

end Category.Internal
