import Playground.Category.Basic
import Playground.Category.Natural_Transformation
import Playground.Category.Instances.MetaCat
import Mathlib.Order.Basic

namespace Category
namespace Instances
section
  def posetCategoryOf (C) [PartialOrder C]
    : Category C where
    hom X Y := PLift (X ≤ Y)
    comp | ⟨f⟩, ⟨g⟩ => ⟨f.trans g⟩
    id X := ⟨le_refl X⟩
    id_comp _ := rfl
    comp_id _ := rfl
    assoc _ _ _ := rfl
end
end Instances
end Category

namespace Category
def asPoset.{u} (C : Type u) [PartialOrder C] := C
instance {C} [h : PartialOrder C] : PartialOrder (asPoset C) := h
instance {C} [PartialOrder C] : Category (asPoset C) := Instances.posetCategoryOf (asPoset C)
end Category