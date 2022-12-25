import Playground.Category.Basic
import Playground.Data.ClassProp

namespace Category

section
  namespace hom
  variable {C} [Category C] {X Y : C} (f : X ⟶ Y) in
  class_prop Epi := ∀ {Z : C} (g h : Y ⟶ Z), (f ≫ g = f ≫ h) → g = h
  end hom

  def Epimorphism {C} [Category C] (X Y : C) := { f : X ⟶ Y // f.Epi }
  scoped infix:80 " ↠ " => Epimorphism
  instance {C} [Category C] {X Y : C} (f : X ↠ Y) : f.val.Epi := f.property
  instance {C} [Category C] {X Y : C} : Coe (X ↠ Y) (X ⟶ Y) where coe := Subtype.val
end

section
  namespace hom
  variable {C} [Category C] {X Y : C} (f : X ⟶ Y) in
  class_prop Mono := ∀ {Z : C} (g h : Z ⟶ X), (g ≫ f = h ≫ f) → g = h
  end hom

  def Monomorphism {C} [Category C] (X Y : C) := { f : X ⟶ Y // f.Mono }
  scoped infix:80 " ↣ " => Monomorphism
  instance {C} [Category C] {X Y : C} (f : X ↣ Y) : f.val.Mono := f.property
  instance {C} [Category C] {X Y : C} : Coe (X ↣ Y) (X ⟶ Y) where coe := Subtype.val
end

section
  def Epimorphism.comp {C} [Category C] {X Y Z : C} (f : X ↠ Y) (g : Y ↠ Z) : X ↠ Z :=
    ⟨f.val ≫ g.val, ⟨by
      intro _ a b hab
      rw [assoc, assoc] at hab
      have hab := f.property.1 _ _ hab
      have hab := g.property.1 _ _ hab
      exact hab⟩⟩

  def Monomorphism.comp {C} [Category C] {X Y Z : C} (f : X ↣ Y) (g : Y ↣ Z) : X ↣ Z :=
    ⟨f.val ≫ g.val, ⟨by
      intro _ a b hab
      rw [←assoc, ←assoc] at hab
      have hab := g.property.1 _ _ hab
      have hab := f.property.1 _ _ hab
      exact hab⟩⟩
end

end Category