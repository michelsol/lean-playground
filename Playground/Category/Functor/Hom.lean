import Playground.Category.Instances.Set
import Playground.Category.Functor.Bi

namespace Category.Functor
section

  def hom.{u,v} (C) [Category.{u,v} C] : Bi Cᵒᵖ C (Type _) where
      obj_map := λ ⟨op X, Y⟩ => X ⟶ Y
      hom_map := @λ ⟨op X₁, Y₁⟩ ⟨op X₂, Y₂⟩ ⟨op f, g⟩ => 
        show (_ ⟶ _) → (_ ⟶ _) from 
        λ z => (f ≫ z) ≫ g
      hom_map_comp := @λ ⟨op X₁, Y₁⟩ ⟨op X₂, Y₂⟩ ⟨op X₃, Y₃⟩ ⟨op f₁, g₁⟩ ⟨op f₂, g₂⟩ => by
        funext (z : _ ⟶ _)
        show ((_ ≫ _) ≫ _) ≫ (_ ≫ _) = (_ ≫ ((_ ≫ _) ≫ _)) ≫ _
        simp [assoc]
      hom_map_id := λ ⟨op X₁, Y₁⟩ => by simp; rfl

  example {C} [Category C] (U : Cᵒᵖ) : C ⥤ Type _ := (hom C).fixLeft U
  example {C} [Category C] (U : C) : Cᵒᵖ ⥤ Type _ := (hom C).fixRight U

  def ulift.{u,v} : Type u ⥤ Type (max u v) := {
      obj_map := ULift.{v}
      hom_map := @λ X Y f => λ x : ULift.{v} X => ULift.up (f x.down)
      hom_map_comp := λ _ _ => rfl
      hom_map_id := λ _ => rfl
    }


end
end Category.Functor