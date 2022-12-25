import Playground.Category.Basic
import Playground.Category.Functor.Basic

namespace Category.Instances
section
  def discreteCategoryOf (I) : Category I where
    hom X Y := PLift (X = Y)
    comp | ⟨h1⟩, ⟨h2⟩ => ⟨h1.trans h2⟩
    id _ := ⟨rfl⟩
    id_comp _ := rfl
    comp_id _ := rfl
    assoc _ _ _ := rfl
end
end Category.Instances

section
  namespace Category
  def asDiscrete.{u} (C : Type u) := C
  instance {C} : Category (asDiscrete C) := Instances.discreteCategoryOf (asDiscrete C)
  end Category
end

section
  open Category
  def List.toDiscreteFunctor {C} [Category C] (l : List C) : asDiscrete (Fin l.length) ⥤ C where
    obj_map := λ i => l.get i
    hom_map := λ ⟨f⟩ => f ▸ 𝟙 _
    hom_map_comp := sorry
    hom_map_id := sorry
end