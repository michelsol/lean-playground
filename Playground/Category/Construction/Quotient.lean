import Playground.Category.Functor.Universal
import Playground.Category.WithZeroMorphisms

namespace Category.Construction
section
  universe u
  variable {X : Type u}
  namespace Quotient2
  structure Data.{v} (R : Setoid X) where
    object : Type v
    morphism : X → object
    sound : ∀ x y : X, x ≈ y → morphism x = morphism y

  structure Data.Hom {R : Setoid X} (A B : Data R) where
    function : A.object ⟶ B.object
    law : A.morphism ≫ function = B.morphism

  example {R : Setoid X} : Category (Data R) where
    hom := Data.Hom
    comp
    | { function := f₁, law := h₁ }, { function := f₂, law := h₂ } =>
      { function := f₁ ≫ f₂, law := by rw [←assoc, h₁, h₂] }
    id A := { function := 𝟙 _, law := rfl }
    id_comp _ := rfl
    comp_id _ := rfl
    assoc _ _ _ := sorry
  end Quotient2
end
end Category.Construction