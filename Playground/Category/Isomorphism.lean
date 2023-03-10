import Playground.Category.Basic

namespace Category

section
  structure Isomorphism {C} [Category C] (U V : C) where
    hom : U â¶ V
    inv : V â¶ U
    hom_inv : hom â« inv = ð _
    inv_hom : inv â« hom = ð _
  scoped infix:80 " â " => Isomorphism

  instance {C} [Category C] {U V : C} : Coe (U â V) (U â¶ V) where
    coe := Isomorphism.hom

end

namespace Isomorphism
section 
  attribute [simp] hom_inv
  attribute [simp] inv_hom
  -- Basic properties of isomorphisms over a fixed category
  variable {C} [Category C]

  def symm {U V : C} (iso : U â V) : V â U where
    hom := iso.inv
    inv := iso.hom
    hom_inv := iso.inv_hom
    inv_hom := iso.hom_inv

  def trans {U V W : C} (h1 : U â V) (h2 : V â W) : U â W := {
      hom := h1.hom â« h2.hom
      inv := h2.inv â« h1.inv
      hom_inv := by
        rw [assoc h1.hom, âassoc h2.hom]
        simp
      inv_hom := by
        rw [assoc h2.inv, âassoc h1.inv]
        simp
    }
end
end Isomorphism

end Category