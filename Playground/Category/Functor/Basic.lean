import Playground.Category.Basic
import Playground.Category.Opposite
import Playground.Category.Isomorphism
import Mathlib.Init.Function
import Std.Logic

namespace Category

section
  structure Functor (C D) [Category C] [Category D] where
    obj_map : C → D
    hom_map {X Y : C} : (X ⟶ Y) → (obj_map X ⟶ obj_map Y)
    hom_map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), hom_map (f ≫ g) = hom_map f ≫ hom_map g
    hom_map_id : ∀ X, hom_map (𝟙 X) = 𝟙 (obj_map X)
  scoped infixr:26 " ⥤ " => Functor
end

namespace Functor
section
  attribute [simp] hom_map_comp
  attribute [simp] hom_map_id

  instance [Category C] [Category D] : CoeFun (C ⥤ D) (λ _ => C → D) where
    coe F := F.obj_map
  -- instance [Category C] [Category D] : CoeFun (C ⥤ D) (λ F => {X Y : C} → (X ⟶ Y) → (F.obj_map X ⟶ F.obj_map Y)) where
  --   coe F := F.hom_map

  def contra (C D) [Category C] [Category D] := Cᵒᵖ ⥤ D

  def Faithful [Category C] [Category D] (F : C ⥤ D) : Prop :=
    ∀ ⦃X Y : C⦄, (F.hom_map : (X ⟶ Y) → _).Injective

  def Full [Category C] [Category D] (F : C ⥤ D) : Prop :=
    ∀ ⦃X Y : C⦄, (F.hom_map : (X ⟶ Y) → _).Surjective

  def isom_images_of_isom_objects [Category C] [Category D] 
    (F : C ⥤ D) (f : X ≅ Y) : F X ≅ F Y := {
    hom := F.hom_map f.hom
    inv := F.hom_map f.inv
    hom_inv := by rw [←hom_map_comp, f.hom_inv, hom_map_id]
    inv_hom := by rw [←hom_map_comp, f.inv_hom, hom_map_id]
  }

  noncomputable
  def isom_objects_of_isom_images_of_FullFaithful [Category C] [Category D] 
    {F : C ⥤ D} (F_full : F.Full) (F_faithful : F.Faithful)
    (g : F X ≅ F Y) : X ≅ Y := {
    hom := (F_full g.hom).choose
    inv := (F_full g.inv).choose
    hom_inv := by
      apply F_faithful
      rw [hom_map_comp]
      rw [(F_full g.hom).choose_spec, (F_full g.inv).choose_spec]
      rw [g.hom_inv, hom_map_id]
    inv_hom := by
      apply F_faithful
      rw [hom_map_comp]
      rw [(F_full g.hom).choose_spec, (F_full g.inv).choose_spec]
      rw [g.inv_hom, hom_map_id]
  }

  theorem eq_of_maps_eq {C D} [Category C] [Category D] 
    {F G : C ⥤ D}
    (h1 : F.obj_map = G.obj_map) (h2 : ∀ {X Y} (f : X ⟶ Y), F.hom_map f = h1 ▸ G.hom_map f) : F = G := by
    cases F with | mk Fobj_map Fhom_map _ _ =>
    cases G with | mk Gobj_map Ghom_map _ _ =>
      dsimp at h1
      subst h1
      dsimp at h2
      simp
      funext X Y f
      exact h2 f

end
end Functor
end Category
