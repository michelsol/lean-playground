import Playground.Category.Basic

namespace Category
section
  class WithZeroArrows (C) [Category C] where
    zero_hom (X Y : C) : X ⟶ Y
  abbrev zero_hom {C} [Category C] [WithZeroArrows C] (X Y : C) : X ⟶ Y := WithZeroArrows.zero_hom X Y
  scoped notation "𝟬" => zero_hom

  class WithZeroMorphisms (C) [Category C] extends WithZeroArrows C where
    comp_zero : ∀ {X Y Z : C}, ∀ f, f ≫ 𝟬 Y Z = 𝟬 X Z
    zero_comp : ∀ {X Y Z : C}, ∀ f, 𝟬 X Y ≫ f = 𝟬 X Z
end
end Category