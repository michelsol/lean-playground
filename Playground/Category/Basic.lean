section 
  -- We define a category and its usual notations

  namespace Category
  class Hom.{u,v} (C : Type u) where
    hom : C → C → Type v
  abbrev hom {C} [Hom C] : C → C → Type _ := Hom.hom
  scoped infix:10 " ⟶ " => hom

  class Data.{u} (C : Type u) extends Hom C where
    comp {X Y Z : C} : (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)
    id (X : C) : X ⟶ X
  abbrev comp {C} [Data C] : {X Y Z : C} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z) := Data.comp
  abbrev id {C} [Data C] : (X : C) → X ⟶ X := Data.id
  scoped infix:80 " ≫ " => comp
  scoped notation "𝟙" => id
  end Category
  
  open Category in
  class Category.{u} (C : Type u) extends Category.Data C where
    id_comp {X Y : C} : ∀ (f : X ⟶ Y), 𝟙 X ≫ f = f
    comp_id {X Y : C} : ∀ (f : X ⟶ Y), f ≫ 𝟙 Y = f
    assoc {X Y Z W : C} : ∀ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W), 
      (f ≫ g) ≫ h = f ≫ (g ≫ h)

end

namespace Category
attribute [simp] id_comp
attribute [simp] comp_id

def hom.source {C} [Category C] {X Y : C} (_ : X ⟶ Y) : C := X
def hom.target {C} [Category C] {X Y : C} (_ : X ⟶ Y) : C := Y

abbrev Large.{u} (C : Type (u+1)) := Category.{u+1,u} C
abbrev Small.{u} (C : Type u) := Category.{u,u} C

end Category