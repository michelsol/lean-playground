import Playground.Category.Instances.Set
import Playground.Category.Functor.Bi

namespace Category.Functor
section
  variable {C D} [Category C] [Category D]

  section
    namespace Universal
    class CanFactorThrough.{u,v,w} (dataType : Type u) where
      objectType : Type v
      objectTypeCategory : Category.{v,w} objectType
      object : dataType → objectType
      FactorsThroughVia (specificData generalData : dataType) (morphism : object specificData ⟶ object generalData) : Prop
      FactorsThroughVia_comp : ∀ {generalData ordinaryData specificData morphism₁ morphism₂}, 
        FactorsThroughVia ordinaryData generalData morphism₁
        → FactorsThroughVia specificData ordinaryData morphism₂
        → FactorsThroughVia specificData generalData (morphism₂ ≫ morphism₁)
      FactorsThroughVia_id : ∀ (data), FactorsThroughVia data data (𝟙 _)
    export CanFactorThrough (FactorsThroughVia FactorsThroughVia_comp FactorsThroughVia_id)
    instance {dataType} [i : CanFactorThrough dataType] : Category (i.objectType) := i.objectTypeCategory
    class Existence {dataType} [CanFactorThrough dataType] (generalData : dataType) : Prop where
      existence : ∀ specificData, ∃ morphism, FactorsThroughVia specificData generalData morphism
    class Uniqueness {dataType} [CanFactorThrough dataType] (generalData : dataType) : Prop where
      uniqueness : ∀ specificData, ∀ ⦃morphism₁ morphism₂⦄,
        FactorsThroughVia specificData generalData morphism₁
        → FactorsThroughVia specificData generalData morphism₂
        → morphism₁ = morphism₂
    class Property {dataType} [CanFactorThrough dataType] (generalData : dataType)
    extends Existence generalData, Uniqueness generalData : Prop
    section
      variable {dataType} [CanFactorThrough dataType] (data₁ data₂ : dataType)
        [h₁ : Property data₁] [h₂ : Property data₂]
      noncomputable def isomorphismOfSolutions
        : CanFactorThrough.object data₁ ≅ CanFactorThrough.object data₂ where
        hom := (h₂.existence _).choose
        inv := (h₁.existence _).choose
        hom_inv := h₁.uniqueness _ (FactorsThroughVia_comp (h₁.existence _).choose_spec (h₂.existence _).choose_spec) (FactorsThroughVia_id _)
        inv_hom := h₂.uniqueness _ (FactorsThroughVia_comp (h₂.existence _).choose_spec (h₁.existence _).choose_spec) (FactorsThroughVia_id _)
      theorem isomorphismOfSolutions_has_property
        : FactorsThroughVia data₁ data₂ (isomorphismOfSolutions data₁ data₂) :=
        (h₂.existence _).choose_spec
      theorem isomorphismOfSolutions_is_unique
        : ∀ ⦃morphism₁ morphism₂⦄, FactorsThroughVia data₁ data₂ morphism₁ → FactorsThroughVia data₁ data₂ morphism₂ → morphism₁ = morphism₂ :=
        h₂.uniqueness data₁
    end
    end Universal
  end

  section
    namespace CoUniversal
    class CanFactorThrough.{u,v,w} (dataType : Type u) where
      objectType : Type v
      objectTypeCategory : Category.{v,w} objectType
      object : dataType → objectType
      FactorsThroughVia (specificData generalData : dataType) (α : object generalData ⟶ object specificData) : Prop
      FactorsThroughVia_comp : ∀ {generalData ordinaryData specificData morphism₁ morphism₂}, 
        FactorsThroughVia ordinaryData generalData morphism₁
        → FactorsThroughVia specificData ordinaryData morphism₂
        → FactorsThroughVia specificData generalData (morphism₁ ≫ morphism₂)
      FactorsThroughVia_id : ∀ (data), FactorsThroughVia data data (𝟙 _)
    export CanFactorThrough (FactorsThroughVia FactorsThroughVia_comp FactorsThroughVia_id)
    instance {dataType} [i : CanFactorThrough dataType] : Category (i.objectType) := i.objectTypeCategory
    class Existence {dataType} [CanFactorThrough dataType] (generalData : dataType) : Prop where
      existence : ∀ specificData, ∃ morphism, FactorsThroughVia specificData generalData morphism
    class Uniqueness {dataType} [CanFactorThrough dataType] (generalData : dataType) : Prop where
      uniqueness : ∀ specificData, ∀ ⦃morphism₁ morphism₂⦄, FactorsThroughVia specificData generalData morphism₁ → FactorsThroughVia specificData generalData morphism₂ → morphism₁ = morphism₂
    class Property {dataType} [CanFactorThrough dataType] (generalData : dataType) extends Existence generalData, Uniqueness generalData : Prop
    section
      variable {dataType} [CanFactorThrough dataType] (data₁ data₂ : dataType)
        [h₁ : Property data₁] [h₂ : Property data₂]
      noncomputable def isomorphismOfSolutions
        : CanFactorThrough.object data₁ ≅ CanFactorThrough.object data₂ where
        hom := (h₁.existence _).choose
        inv := (h₂.existence _).choose
        hom_inv := h₁.uniqueness _ (FactorsThroughVia_comp (h₁.existence _).choose_spec (h₂.existence _).choose_spec) (FactorsThroughVia_id _)
        inv_hom := h₂.uniqueness _ (FactorsThroughVia_comp (h₂.existence _).choose_spec (h₁.existence _).choose_spec) (FactorsThroughVia_id _)
      theorem isomorphismOfSolutions_has_property
        : FactorsThroughVia data₂ data₁ (isomorphismOfSolutions data₁ data₂) :=
        (h₁.existence _).choose_spec
      theorem isomorphismOfSolutions_is_unique
        : ∀ ⦃morphism₁ morphism₂⦄, FactorsThroughVia data₁ data₂ morphism₁ → FactorsThroughVia data₁ data₂ morphism₂ → morphism₁ = morphism₂ :=
        h₂.uniqueness data₁
    end
    end CoUniversal
  end

  section
    variable (F : C ⥤ D) (X : D)
    namespace Universal
    structure Data where
      object : C
      morphism : F object ⟶ X
    instance : CanFactorThrough (Data F X) where
      FactorsThroughVia specificData generalData morphism :=
        F.hom_map morphism ≫ generalData.morphism = specificData.morphism
      FactorsThroughVia_comp {generalData ordinaryData specificData morphism₁ morphism₂}
        (h₁ : _ = _) (h₂ : _ = _) := show _ = _ from
        F.hom_map_comp .. ▸ assoc _ _ generalData.morphism ▸ h₁ ▸ h₂
      FactorsThroughVia_id := by simp
    end Universal
    structure Universal extends Universal.Data F X, Universal.Property toData
  end

  section
    variable (F : C ⥤ D) (X : D)
    namespace CoUniversal
    structure Data where
      object : C
      morphism : X ⟶ F object
    instance : CanFactorThrough (Data F X) where
      FactorsThroughVia specificData generalData morphism :=
        generalData.morphism ≫ F.hom_map morphism = specificData.morphism
      FactorsThroughVia_comp {generalData ordinaryData specificData morphism₁ morphism₂}
        (h₁ : _ = _) (h₂ : _ = _) := show _ = _ from
      F.hom_map_comp .. ▸ assoc generalData.morphism .. ▸ h₁ ▸ h₂
      FactorsThroughVia_id := by simp
    end CoUniversal
    structure CoUniversal extends CoUniversal.Data F X, CoUniversal.Property toData
  end

  -- def CoUniversalElement.{u} (F : Cᵒᵖ ⥤ Type u) := CoUniversal F PUnit
  structure CoUniversal.Element.{u} (F : Cᵒᵖ ⥤ Type u) where
    object : C
    element : F (op object)
    property : ∀ ⦃O⦄ (f : F (op O)), ∃! α : O ⟶ object, F.hom_map α.op element = f

end
end Category.Functor


namespace Category.Functor
def Δ (C) [Category C] (I) [Category I] : C ⥤ I ⥤ C := {
  obj_map := λ X => {
    obj_map := λ _ => X
    hom_map := λ _ => 𝟙 X
    hom_map_comp := by simp
    hom_map_id := by simp
  }
  hom_map := λ f => {
    component := λ _ => f
    naturality := by simp
  }
  hom_map_comp := λ _ _ => rfl
  hom_map_id := λ _ => rfl
}

theorem Δ_obj_map_eq_Δ_at_comp
  {C} [Category C] (I) [Category I] {D} [Category D]
  (F : C ⥤ D)  (U : C)
  : Δ D I (F U) = Δ C I U ⋙ F := 
  eq_of_maps_eq (by funext _; rfl)
  (by
  intro X Y _
  show 𝟙 (F _) = F.hom_map (𝟙 _)
  rw [hom_map_id])


def Cone {C} [Category C] {I} [Category I] (X : I ⥤ C) (obj : C) := Δ C I obj ⟶ X
def CoCone {C} [Category C] {I} [Category I] (X : I ⥤ C) (obj : C) := X ⟶ Δ C I obj

def Limit {C} [Category C] {I} [Category I] := Functor.Universal (Δ C I)
def CoLimit {C} [Category C] {I} [Category I] := Functor.CoUniversal (Δ C I)

def PreservesLimitsOfDiagram {C} [Category C] {I} [Category I] {D} [Category D]
  (F : C ⥤ D) (X : I ⥤ C) -- diagram
  : Prop := ∀ L : Limit X, ∃ M : Limit (X ⋙ F), M.toData = {
    object := F L.object
    morphism := Δ_obj_map_eq_Δ_at_comp I F L.object ▸ ((compRight I F).hom_map L.morphism)
  }

def PreservesLimitsOfShape {C} [Category C] (I) [Category I] {D} [Category D]
  (F : C ⥤ D) : Prop := ∀ (X : I ⥤ C), F.PreservesLimitsOfDiagram X

def PreservesLimits {C} [Category C] {D} [Category D]
  (F : C ⥤ D) : Prop := ∀ {I : Type} {_ : Category.Small I}, F.PreservesLimitsOfShape I

end Category.Functor

section
namespace Category
  def Complete (C) [Category C] : Prop := ∀ {I : Type} {_ : Category.Small I} (X : I ⥤ C), Nonempty (Functor.Limit X)
end Category
end
