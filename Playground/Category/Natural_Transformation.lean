import Playground.Category.Basic
import Playground.Category.Opposite
import Playground.Category.Isomorphism
import Playground.Category.Functor.Basic

namespace Category

section
  structure Natural_Transformation {C D} [Category C] [Category D] (F G : C ⥤ D) where
    component (X : C) : F X ⟶ G X
    naturality {X Y : C} : ∀ f : X ⟶ Y, F.hom_map f ≫ component Y = component X ≫ G.hom_map f
  scoped infixr:26 " ⟹ " => Natural_Transformation
end

namespace Natural_Transformation
section
  instance {C D} [Category C] [Category D] {F G : C ⥤ D}
    : CoeFun (F ⟹ G) (λ _ => (X : C) → (F X ⟶ G X)) where
    coe α := α.component

  theorem eq_of_component_eq {C D} [Category C] [Category D] 
    {F G : C ⥤ D} {α β : F ⟹ G} 
    (h : α.component = β.component) : α = β := by
    cases α; cases β; simp; exact h

end
end Natural_Transformation
end Category