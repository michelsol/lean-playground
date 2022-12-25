import Playground.Category.Functor.Limit.Product
import Playground.Category.Instances.Set
import Playground.Category.Instances.Discrete

namespace Category.Construction
section
  open Functor
  open Functor.Limit.Product

  variable {C} [Category C] {I} (X : Diagram C I)
  namespace Product
  structure Data where
    object : C
    morphism : (i : _) → object ⟶ X i
  instance : Universal.CanFactorThrough (Data X) where
    FactorsThroughVia specificData generalData morphism :=
      ∀ i, morphism ≫ generalData.morphism i = specificData.morphism i
    FactorsThroughVia_comp {generalData ordinaryData specificData morphism₁ morphism₂}
      (h₁ : ∀ i, _ = _) (h₂ : ∀ i, _ = _) := show ∀ i, _ = _ from
      λ i => assoc _ morphism₁ _ ▸ h₁ i ▸ h₂ i
    FactorsThroughVia_id := by simp
  end Product
  structure Product extends Product.Data X, Universal.Property toData
end
section
  open Functor.Limit.Product
  def productOfProductType.{u} {I : Type u} (X : Diagram (Type u) I) : Product X where
    object := ∀ k, X k
    morphism i prod := prod i
    existence
    | ⟨_, f⟩ => ⟨λ y k => f k y, λ _ => rfl⟩
    uniqueness
    | ⟨_, f⟩, α, β, hα, hβ => 
      funext λ y => funext λ k =>
      have hα : α .. = f .. := congrFun (hα k) y
      have hβ : β .. = f .. := congrFun (hβ k) y
      hβ ▸ hα
end
end Category.Construction
namespace Category
section
  open Natural_Transformation
  open Functor.Limit.Product

  def Functor.Limit.Product.toConstructionProduct {C} [Category C] {I} {X : Diagram C I} (p : Product X)
    : Construction.Product X where
    object := p.object
    morphism := p.morphism.component
    existence
    | ⟨O, f⟩ =>
      have ⟨α, hα⟩ := p.existence ⟨_, {component := f, naturality := 
          λ {i j} ⟨hij⟩ => 
          have : PLift.up rfl = 𝟙 i := rfl
          by { subst hij; rw [this]; simp }}⟩
      ⟨α, λ i =>
          have hα := congrArg component hα
          have hα := congrFun hα i
          hα⟩
    uniqueness
    | ⟨O, f⟩, α, β, hα, hβ => 
      p.uniqueness ⟨_, {component := f, naturality := 
          λ {i j} ⟨hij⟩ => 
          have : PLift.up rfl = 𝟙 i := rfl
          by { subst hij; rw [this]; simp }}⟩
      (eq_of_component_eq <| funext hα) (eq_of_component_eq <| funext hβ)

  def Construction.Product.toLimitProduct {C} [Category C] {I} {X : Diagram C I} (p : Product X)
    : Functor.Limit.Product X where
    object := p.object
    morphism := { 
        component := p.morphism
        naturality := λ {i j} ⟨hij⟩ =>
          have : PLift.up rfl = 𝟙 i := rfl
          by subst hij; rw [this]; simp}
    existence
    | ⟨O, (f : _ ⟹ _)⟩ =>
      have ⟨α, hα⟩ := p.existence ⟨_, f.component⟩
      sorry
    uniqueness
    | ⟨O, (f : _ ⟹ _)⟩, α, β, hα, hβ =>
      sorry

end
end Category