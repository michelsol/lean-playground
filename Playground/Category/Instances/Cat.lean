import Playground.Category.Instances.MetaCat

namespace Category.Instances
section
  -- Here we define Cat, the category of categories, as a math object, hence in a fixed universe
  universe u v in
  instance Cat : Category (Σ C, Category.{u,v} C) where
    hom := λ ⟨C, _⟩ ⟨D, _⟩ => MetaCat.hom C D
    comp := @λ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ => MetaCat.comp
    id := λ ⟨_, _⟩ => MetaCat.id _
    id_comp := @λ ⟨_, _⟩ ⟨_, _⟩ => MetaCat.id_comp
    comp_id := @λ ⟨_, _⟩ ⟨_, _⟩ => MetaCat.comp_id
    assoc := @λ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ => MetaCat.assoc

  def Cat.Isomorphism (C D) [Category C] [Category D] := 
    Category.Isomorphism (C := Σ C, Category C) ⟨C, inferInstance⟩ ⟨D, inferInstance⟩

end
end Category.Instances