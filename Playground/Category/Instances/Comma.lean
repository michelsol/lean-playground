import Playground.Category.Basic
import Playground.Category.Natural_Transformation
import Playground.Category.Instances.MetaCat

namespace Category
namespace Instances
section

  variable {C D E} [Category C] [Category D] [Category E]

  def commaCategory (F : C ⥤ E) (G : D ⥤ E) 
    : Category (Σ X Y, F X ⟶ G Y) where
    hom := λ ⟨X₁, Y₁, α₁⟩ ⟨X₂, Y₂, α₂⟩ =>
      Σ' (β : X₁ ⟶ X₂) (γ : Y₁ ⟶ Y₂),
      F.hom_map β ≫ α₂ = α₁ ≫ G.hom_map γ
    comp := @λ ⟨X₁, Y₁, α₁⟩ ⟨X₂, Y₂, α₂⟩ ⟨X₃, Y₃, α₃⟩ ⟨β₁, γ₁, h₁⟩ ⟨β₂, γ₂, h₂⟩ =>
      let β := β₁ ≫ β₂
      let γ := γ₁ ≫ γ₂
      have h : F.hom_map (β₁ ≫ β₂) ≫ α₃ = α₁ ≫ G.hom_map (γ₁ ≫ γ₂) := by
        rw [F.hom_map_comp, G.hom_map_comp]
        rw [assoc, h₂, ←assoc, h₁, assoc]
      ⟨β, γ, h⟩
    id := λ ⟨X, Y, α⟩ => ⟨𝟙 _, 𝟙 _, by simp⟩
    id_comp := sorry
    comp_id := sorry
    assoc := sorry

end
end Instances

end Category
