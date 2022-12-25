import Playground.Category.Basic

namespace Category

section
  structure Isomorphism {C} [Category C] (U V : C) where
    hom : U ⟶ V
    inv : V ⟶ U
    hom_inv : hom ≫ inv = 𝟙 _
    inv_hom : inv ≫ hom = 𝟙 _
  scoped infix:80 " ≅ " => Isomorphism

  instance {C} [Category C] {U V : C} : Coe (U ≅ V) (U ⟶ V) where
    coe := Isomorphism.hom

end

namespace Isomorphism
section 
  attribute [simp] hom_inv
  attribute [simp] inv_hom
  -- Basic properties of isomorphisms over a fixed category
  variable {C} [Category C]

  def symm {U V : C} (iso : U ≅ V) : V ≅ U where
    hom := iso.inv
    inv := iso.hom
    hom_inv := iso.inv_hom
    inv_hom := iso.hom_inv

  def trans {U V W : C} (h1 : U ≅ V) (h2 : V ≅ W) : U ≅ W := {
      hom := h1.hom ≫ h2.hom
      inv := h2.inv ≫ h1.inv
      hom_inv := by
        rw [assoc h1.hom, ←assoc h2.hom]
        simp
      inv_hom := by
        rw [assoc h2.inv, ←assoc h1.inv]
        simp
    }
end
end Isomorphism

end Category