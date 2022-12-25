import Playground.Category.Basic
import Playground.Category.Functor.Basic

namespace Category.Instances
section
  namespace MetaCat
  -- Here we "define" MetaCat or CAT, the category of all categories in all universes
  -- as a set of top-level definitions because it is NOT a math object because of usual paradoxes
  def hom (C D) [Category C] [Category D] : Type _ := C ⥤ D

  def comp {C D E} [Category C] [Category D] [Category E] 
    (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
    obj_map X := G.obj_map (F.obj_map X)
    hom_map {X Y} f := G.hom_map (F.hom_map f)
    hom_map_comp := by simp
    hom_map_id := by simp

  def id (C) [Category C] : C ⥤ C where
    obj_map := λ X => X
    hom_map := λ F => F
    hom_map_comp := λ _ _ => rfl
    hom_map_id := λ _ => rfl

  end MetaCat
end
end Category.Instances
namespace Category
scoped notation:max " 𝟭 " => Instances.MetaCat.id
scoped infixr:80 " ⋙ " => Instances.MetaCat.comp
end Category
namespace Category.Instances
section
  namespace MetaCat
  @[simp]
  def id_comp {C D} [Category C] [Category D] : ∀ F : C ⥤ D, 𝟭 C ⋙ F = F :=
    λ _ => rfl

  @[simp]
  def comp_id {C D} [Category C] [Category D] : ∀ F : C ⥤ D, F ⋙ 𝟭 D = F :=
    λ _ => rfl
  
  def assoc {B C D E} [Category B] [Category C] [Category D] [Category E]
    : ∀ (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E), (F ⋙ G) ⋙ H = F ⋙ (G ⋙ H) :=
    λ _ _ _ => rfl

  structure Isomorphism (C D) [Category C] [Category D] where
    hom : C ⥤ D
    inv : D ⥤ C
    hom_inv : comp hom inv = id _
    inv_hom : comp inv hom = id _
  end MetaCat
end
end Category.Instances