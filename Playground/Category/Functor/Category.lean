import Playground.Category.Basic
import Playground.Category.Opposite
import Playground.Category.Isomorphism
import Playground.Category.Functor.Basic
import Playground.Category.Natural_Transformation
import Playground.Category.Instances.Cat
import Std.Tactic.Ext

namespace Category.Functor
open Natural_Transformation

section
  -- We define the functor category [C, D]
  instance {C D} [Category C] [Category D] : Category (C ⥤ D) where
    hom F G := F ⟹ G
    comp {F G H} (α : F ⟹ G) (β : G ⟹ H) := {
        component := λ X => α X ≫ β X
      , naturality := λ {X Y} f => by
          show F.hom_map f ≫ (α Y ≫ β Y) = (α X ≫ β X) ≫ H.hom_map f
          rw [←assoc, α.naturality, assoc, β.naturality, assoc]
      }
    id F := {
        component := λ X => 𝟙 (F X)
      , naturality := λ {X Y} f => by
          show F.hom_map _ ≫ 𝟙 _ = 𝟙 _ ≫ F.hom_map _
          simp
      }
    id_comp {F G} (α : F ⟹ G) := by
      apply eq_of_component_eq
      ext X
      show 𝟙 _ ≫ _ = _
      simp
    comp_id {F G} (α : F ⟹ G) := by
      apply eq_of_component_eq
      ext X
      show _ ≫ 𝟙 _ = _
      simp
    assoc {F G H I} (α : F ⟹ G) (β : G ⟹ H) (γ : H ⟹ I) := by
      apply eq_of_component_eq
      ext X
      show (_ ≫ _) ≫ _ = _ ≫ (_ ≫ _)
      rw [assoc]
    
  @[simp] theorem component_comp {C D} [Category C] [Category D]
    {F G H : C ⥤ D} (α : F ⟹ G) (β : G ⟹ H) (X : C)
    : (α ≫ β : F ⟶ H).component X = α X ≫ β X := rfl
end

section

  def opp {C D} [Category C] [Category D] : (C ⥤ D) → (Cᵒᵖ ⥤ Dᵒᵖ) := λ F => {
      obj_map := λ (op X) => op $ F.obj_map X
      hom_map := λ (op f) => (F.hom_map f).op
      hom_map_comp := λ _ _ => by simp
      hom_map_id := λ _ => by simp; rfl
    }

end

section
  def compRight (C) [Category C] {D} [Category D] {E} [Category E] (H : D ⥤ E) : (C ⥤ D) ⥤ (C ⥤ E) where
    obj_map F := F ⋙ H
    hom_map {F G} (α : F ⟹ G) := 
      show _ ⋙ _ ⟹ _ ⋙ _ from {
        component := λ X => H.hom_map (α X)
        naturality := λ {X Y} f => by
          dsimp
          sorry
      }
    hom_map_comp := sorry
    hom_map_id := sorry

end
end Category.Functor