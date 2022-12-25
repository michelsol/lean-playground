import Playground.Category.Functor.Hom
import Playground.Category.Instances.MetaCat

namespace Category.Functor
section

  def yoneda (C) [Category C] : C ⥤ Cᵒᵖ ⥤ Type _ := (hom C).swap.curry

  namespace yoneda
  -- define yoneda's lemma's pairing bifunctor: X, F ↦ (hom(_,X) ⟹ F)
  def pairing (C) [Category.{u,v} C] : Bi Cᵒᵖ (Cᵒᵖ ⥤ Type v) (Type (max u v)) :=
    (yoneda C).opp.prod (𝟭 (Cᵒᵖ ⥤ Type _)) ⋙ hom (Cᵒᵖ ⥤ Type _)

  def evaluation.{u,v} (C) [Category.{u,v} C] : Bi Cᵒᵖ (Cᵒᵖ ⥤ Type v) (Type (max u v)) :=
    Bi.evaluation Cᵒᵖ (Type v) ⋙ Functor.ulift.{v,u}

  -- This is yoneda's lemma stated compactly as an explicit natural isomorphism
  open Natural_Transformation in
  def isomorphism.{u,v} (C) [Category.{u,v} C] : pairing C ≅ evaluation C := {
      hom := {
        component := λ ⟨op U, P⟩ => λ (s : yoneda _ U ⟹ P) => 
          show ULift $ P (op U) from
          ULift.up $ s (op U) (𝟙 U)
        naturality := @λ ⟨op U₁, P₁⟩ ⟨op U₂, P₂⟩ ⟨op f, α⟩ => by
          funext (s : _ ⟹ P₁)
          apply congrArg ULift.up
          apply congrArg (α.component (op U₂))
          show (s (op U₂) ((𝟙 _ ≫ 𝟙 _) ≫ f)) = (s (op U₁) ≫ P₁.hom_map (op f)) (𝟙 U₁)
          rw [←s.naturality]
          show (s (op U₂) ((𝟙 _ ≫ 𝟙 _) ≫ f)) = (s (op U₂) ((f ≫ 𝟙 _) ≫ 𝟙 _))
          simp
      }
      inv := {
        component := λ ⟨op U, P⟩ => λ (⟨ξ⟩ : ULift $ P (op U)) => show yoneda _ U ⟹ P from {
          component := λ (op V) => λ f => P.hom_map f.op ξ
          naturality := @λ (op V₁) (op V₂) (op g) => by
            funext (f : _ ⟶ _)
            show P.hom_map ((g ≫ f) ≫ 𝟙 U).op ξ = (P.hom_map f.op ≫ P.hom_map g.op) ξ
            apply congrFun
            simp
        }
        naturality := @λ ⟨op U₁, P₁⟩ ⟨op U₂, P₂⟩ ⟨op f, (α : _ ⟹ _)⟩ => by
          funext ⟨ξ⟩
          apply eq_of_component_eq
          funext (op V)
          funext g
          show (P₁.hom_map f.op ≫ (α (op U₂) ≫ P₂.hom_map g.op)) ξ
            = (P₁.hom_map (f.op ≫ (𝟙 _ ≫ g).op) ≫ α (op V)) ξ
          rw [←α.naturality]
          simp
          rfl
      }
      inv_hom := by
        apply eq_of_component_eq
        funext ⟨op U, P⟩
        funext (⟨ξ⟩ : ULift $ P (op U))
        apply congrArg ULift.up
        show (P.hom_map (𝟙 _) ξ) = ξ
        rw [hom_map_id]
        rfl
      hom_inv := by
        apply eq_of_component_eq
        funext ⟨op U, P⟩
        funext (s : yoneda _ U ⟹ P)
        apply eq_of_component_eq
        funext (op V)
        funext (f : _ ⟶ _)
        show (s (op U) ≫ P.hom_map f.op) (𝟙 U) = s (op V) f
        rw [←naturality]
        show ((yoneda _ U).hom_map f.op ≫ s (op V)) (𝟙 U) = s (op V) f
        apply congrArg (s (op V))
        show _ ≫ 𝟙 U = f
        simp
    }

  open Natural_Transformation in
  theorem hom_map_eq_isomorphism_inv_component {C} [Category C] (U V : C)
    : (yoneda C).hom_map = ((isomorphism C).inv.component (op U, yoneda C V)) ∘ ULift.up := by
    funext _
    apply eq_of_component_eq
    funext _ _
    show (𝟙 _ ≫ _) ≫ _ = _ ≫ 𝟙 _
    simp

  def isomorphismAt.{u,v} {C} [Category.{u,v} C] (U : C) (P : Cᵒᵖ ⥤ Type v) 
    : (yoneda C U ⟹ P) ≅ (ULift.{u,v} $ P (op U)) :=
      isom_images_of_isom_functors (isomorphism C) (op U, P)

  theorem isomorphism_inv_at_eq_isomorphismAt_inv.{u,v} {C} [Category.{u,v} C] (U : C) (P : Cᵒᵖ ⥤ Type v)
    : (isomorphism C).inv.component (op U, P) = (isomorphismAt U P).inv := by
    simp [isom_images_of_isom_functors, isomorphismAt, isom_images_of_isom_objects]
    simp [Bi.fixLeft, Bi.evaluation, Bi.swap]
    simp [uncurry]
    rfl

  theorem faithful {C} [Category C] : (yoneda C).Faithful := by
    intro U V
    rw [hom_map_eq_isomorphism_inv_component]
    rw [isomorphism_inv_at_eq_isomorphismAt_inv]
    apply flip Function.Injective.comp (λ _ _ => congrArg ULift.down)
    exact Function.LeftInverse.injective <| congrFun <| (isomorphismAt U (yoneda C V)).inv_hom

  theorem full {C} [Category C] : (yoneda C).Full := by
    intro U V
    rw [hom_map_eq_isomorphism_inv_component]
    rw [isomorphism_inv_at_eq_isomorphismAt_inv]
    apply flip Function.Surjective.comp (λ ⟨y⟩ => ⟨y, rfl⟩)
    exact Function.RightInverse.surjective <| congrFun <| (isomorphismAt U (yoneda C V)).hom_inv


  -- yoneda corollary 2: structure of arrows to U is same as structure of arrows to V iff U is same as V
  theorem isomorphism_of_yoneda_isomorphism {C} [Category C] (U V : C) 
    : yoneda C U ≅ yoneda C V → U ≅ V := 
    (yoneda C).isom_objects_of_isom_images_of_FullFaithful full faithful

  end yoneda

end
end Category.Functor