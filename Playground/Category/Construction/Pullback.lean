import Playground.Category.Functor.Universal

namespace Category.Construction
section
  open Functor

  variable {C} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y)
  namespace Pullback
  structure Data where
    object : C
    morphism₁ : object ⟶ X
    morphism₂ : object ⟶ Z
    commutative : morphism₁ ≫ f = morphism₂ ≫ g -- this is part of morphism in the relevant category
  instance : Universal.CanFactorThrough (Data f g) where
    objectType := C
    object := Data.object
    FactorsThroughVia f d α := α ≫ d.morphism₁ = f.morphism₁ ∧ α ≫ d.morphism₂ = f.morphism₂
    FactorsThroughVia_comp {f d f' α α'} (hα : _ ∧ _) (hα' : _ ∧ _) := show _ ∧ _ from
      ⟨assoc _ α _ ▸ hα.1 ▸ hα'.1, assoc _ α _ ▸ hα.2 ▸ hα'.2⟩
    FactorsThroughVia_id := by simp
  end Pullback
  structure Pullback extends Pullback.Data f g, Universal.Property toData
end
section
  class Pullbacks (C) [Category C] where
    pullbackOf {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) : Pullback f g
  export Pullbacks (pullbackOf)
  scoped infixr:35 " ̲× "  => pullbackOf
  instance (C) [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) 
    : Coe (Pullback f g) C where coe x := x.object
end
end Category.Construction
namespace Category
section
variable {C} [Category C]
variable {X Y Z : C}

def PullbackDiagram.Shape (f : X ⟶ Y) (g : Z ⟶ Y) := Fin 3

variable (f : X ⟶ Y) (g : Z ⟶ Y)

def PullbackDiagram.Shape.instance : Category (Fin 3) where
  hom | 0, 0 => Σ' c, c = 𝟙 X
      | 0, 1 => Σ' c, c = f
      | 0, 2 => Empty
      | 1, 0 => Empty
      | 1, 1 => Σ' c, c = 𝟙 Y
      | 1, 2 => Empty
      | 2, 0 => Empty
      | 2, 1 => Σ' c, c = g
      | 2, 2 => Σ' c, c = 𝟙 Z
  comp := λ {U V W} a b => match U, V, W, a, b with
    | 0, 0, 0, ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ≫ b, ha.symm ▸ hb.symm ▸ id_comp _⟩
    | 0, 0, 1, ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ≫ b, ha.symm ▸ hb.symm ▸ id_comp _⟩
    | 0, 1, 1, ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ≫ b, ha.symm ▸ hb.symm ▸ comp_id _⟩
    | 1, 1, 1, ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ≫ b, ha.symm ▸ hb.symm ▸ id_comp _⟩
    | 2, 1, 1, ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ≫ b, ha.symm ▸ hb.symm ▸ comp_id _⟩
    | 2, 2, 1, ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ≫ b, ha.symm ▸ hb.symm ▸ id_comp _⟩
    | 2, 2, 2, ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ≫ b, ha.symm ▸ hb.symm ▸ id_comp _⟩
    | _, _, _, _, _ => sorry
  id  | 0 => ⟨𝟙 _, rfl⟩
      | 1 => ⟨𝟙 _, rfl⟩
      | 2 => ⟨𝟙 _, rfl⟩
  id_comp := sorry
  comp_id := sorry
  assoc := sorry


instance : Category (PullbackDiagram.Shape f g) := PullbackDiagram.Shape.instance f g

def PullbackDiagram := PullbackDiagram.Shape f g ⥤ C

end
end Category