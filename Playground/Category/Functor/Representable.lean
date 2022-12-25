import Playground.Category.Functor.Yoneda
import Playground.Category.Functor.Universal

namespace Category.Functor
section

  -- a functor is representable if its isomorphic to arrows into/out of some object
  def Representation {C} [Category C] (F : Cᵒᵖ ⥤ Type _) := Σ U, yoneda C U ≅ F

  namespace Representation
  section

    def object {C} [Category C] {F : Cᵒᵖ ⥤ Type _} (h : F.Representation) : C :=
      h.1

    def isomorphism {C} [Category C] {F : Cᵒᵖ ⥤ Type _} (h : F.Representation)
      : yoneda C h.object ≅ F :=
      h.2

    theorem isom_objects_of_Representations {C} [Category C] (F : Cᵒᵖ ⥤ Type _) 
      (f : F.Representation) (g : F.Representation) : f.object ≅ g.object := 
      yoneda.isomorphism_of_yoneda_isomorphism f.object g.object
        (f.isomorphism.trans g.isomorphism.symm)

    def transformation {C} [Category C] {F : Cᵒᵖ ⥤ Type _} (h : F.Representation)
      : yoneda C h.object ⟹ F :=
      h.isomorphism.hom

    def element {C} [Category C] {F : Cᵒᵖ ⥤ Type _} (h : F.Representation)
      : F (op h.object) := 
      ((yoneda.isomorphismAt h.object F).hom h.transformation).down

    -- yoneda lemma corollary 3 : a representation corresponds to a universal element
    open Natural_Transformation in
    def UniversalElement {C} [Category C] {F : Cᵒᵖ ⥤ Type _} (h : F.Representation)
      : CoUniversal.Element F where
      object := h.object
      element := h.element
      property := 
      by
        intro O
        let g : (O ⟶ h.object) → F (op O) := λ f => F.hom_map f.op h.element
        suffices g.Bijective from Function.Bijective.existsUnique this
        let g2 : (O ⟶ h.object) → F (op O) := 
          ((yoneda.isomorphismAt h.object F).inv (ULift.up h.element)) (op O)
        have : g = g2 := by
          simp [isom_images_of_isom_functors, yoneda.isomorphismAt, isom_images_of_isom_objects]
          simp [Bi.fixLeft, Bi.evaluation, Bi.swap]
          simp [uncurry]
          rfl
        rw [this]
        dsimp -- use isom_images_of_isom_functors on the inverse isomorphism to complete the proof
        sorry
  end
  end Representation

end
end Category.Functor