import Playground.Category.Basic
import Playground.Category.Natural_Transformation
import Playground.Category.Instances.MetaCat

namespace Category
namespace Instances
section

  instance {C D} [Category C] [Category D] : Category (C × D) where
    hom := λ ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ => (X₁ ⟶ Y₁) × (X₂ ⟶ Y₂)
    comp := @λ ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨Z₁, Z₂⟩ ⟨f₁, f₂⟩ ⟨g₁, g₂⟩ => ⟨f₁ ≫ g₁, f₂ ≫ g₂⟩
    id := λ ⟨X₁, X₂⟩ => ⟨𝟙 X₁, 𝟙 X₂⟩
    id_comp := @λ ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩ => by show (_ ≫ _, _ ≫ _) = _; simp
    comp_id := @λ ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩ => by show (_ ≫ _, _ ≫ _) = _; simp
    assoc := @λ ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨Z₁, Z₂⟩ ⟨W₁, W₂⟩ ⟨f₁, f₂⟩ ⟨g₁, g₂⟩ ⟨h₁, h₂⟩ => by
      show ((_ ≫ _) ≫ _, (_ ≫ _) ≫ _) = (_ ≫ (_ ≫ _), _ ≫ (_ ≫ _))
      simp [assoc]

end
end Instances

end Category
