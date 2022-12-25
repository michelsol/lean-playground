import Playground.Category.Basic

namespace Category

section
  structure Opposite.{u} (α : Type u) where
    unop : α
  export Opposite (unop)
  postfix:max "ᵒᵖ" => Opposite
  @[match_pattern] def op {C} : C → Cᵒᵖ := Opposite.mk

end

section
  instance {C} [Hom C] : Hom Cᵒᵖ where
    hom := λ (op X) (op Y) => (Y ⟶ X)ᵒᵖ

  @[match_pattern] def hom.op {C} [Hom C] {X Y : C} : (X ⟶ Y) → (op Y ⟶ op X) := Opposite.mk

  instance {C} [Data C] : Data Cᵒᵖ where
    comp := @λ (op X) (op Y) (op Z) (op g) (op f) => (f ≫ g).op
    id := λ (op X) => (𝟙 X).op

  @[simp] theorem op_comp_eq {C} [Data C] : 
    ∀ {X Y Z : C}, ∀ f : X ⟶ Y, ∀ g : Y ⟶ Z, (f ≫ g).op = hom.op g ≫ hom.op f :=
    λ _ _ => rfl

  instance {C} [Category C] : Category Cᵒᵖ where
    id_comp := @λ (op X) (op Y) (op f) => congrArg hom.op <| comp_id f
    comp_id := @λ (op X) (op Y) (op f) => congrArg hom.op <| id_comp f
    assoc _ _ _ := congrArg hom.op <| (assoc ..).symm
end

end Category