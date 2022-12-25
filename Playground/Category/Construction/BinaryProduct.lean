import Playground.Category.Basic
import Playground.Category.Construction.Product

namespace Category.Construction
section
  open Functor

  variable {C} [Category C] (X₁ X₂ : C)
  namespace BinaryProduct
  structure Data where
    object : C
    morphism₁ : object ⟶ X₁
    morphism₂ : object ⟶ X₂
  instance : Universal.CanFactorThrough (Data X₁ X₂) where
    FactorsThroughVia f d α := α ≫ d.morphism₁ = f.morphism₁ ∧ α ≫ d.morphism₂ = f.morphism₂
    FactorsThroughVia_comp {f d f' α α'} (hα : _ ∧ _) (hα' : _ ∧ _) := show _ ∧ _ from
      ⟨assoc _ α _ ▸ hα.1 ▸ hα'.1, assoc _ α _ ▸ hα.2 ▸ hα'.2⟩
    FactorsThroughVia_id := by simp
  end BinaryProduct
  structure BinaryProduct extends BinaryProduct.Data X₁ X₂, Universal.Property toData
end

section
  class BinaryProducts (C) [Category C] where
    binaryProductOf (X₁ X₂ : C) : BinaryProduct X₁ X₂
  export BinaryProducts (binaryProductOf)
end

def BinaryProduct.toProduct (C) [Category C] (X₁ X₂ : C) (h : BinaryProduct X₁ X₂)
  : Product [X₁, X₂].toDiscreteFunctor where
  object := h.object
  morphism := λ | ⟨0, _⟩ => h.morphism₁ | ⟨1, _⟩ => h.morphism₂
  existence 
  | ⟨O, f⟩ =>
    let ⟨α, hα⟩ := h.existence ⟨_, (f ⟨0, by simp⟩), (f ⟨1, by simp⟩)⟩
    ⟨α, λ | ⟨0, _⟩ => hα.1 | ⟨1, _⟩ => hα.2⟩
  uniqueness
  | ⟨O, f⟩, α, β, hα, hβ => 
    h.uniqueness ⟨_, (f ⟨0, by simp⟩), (f ⟨1, by simp⟩)⟩
      ⟨hα ⟨0, by simp⟩, hα ⟨1, by simp⟩⟩
      ⟨hβ ⟨0, by simp⟩, hβ ⟨1, by simp⟩⟩

def Product.toBinaryProduct (C) [Category C] (X₁ X₂ : C) (h : Product [X₁, X₂].toDiscreteFunctor)
  : BinaryProduct X₁ X₂ where
  object := h.object
  morphism₁ := h.morphism ⟨0, by simp⟩
  morphism₂ := h.morphism ⟨1, by simp⟩
  existence 
  | ⟨O, f₁, f₂⟩ =>
    let ⟨α, hα⟩ := h.existence ⟨_, (λ | ⟨0, _⟩ => f₁ | ⟨1, _⟩ => f₂)⟩
    ⟨α, ⟨hα ⟨0, by simp⟩, hα ⟨1, by simp⟩⟩⟩
  uniqueness
  | ⟨O, f₁, f₂⟩, α, β, hα, hβ =>
    h.uniqueness ⟨_, (λ | ⟨0, _⟩ => f₁ | ⟨1, _⟩ => f₂)⟩
    (λ | ⟨0, _⟩ => hα.1 | ⟨1, _⟩ => hα.2)
    (λ | ⟨0, _⟩ => hβ.1 | ⟨1, _⟩ => hβ.2)

end Category.Construction