import Playground.Category.Basic

namespace Category.Instances
section
  -- Here we define SET, the category of all types in all universes
  -- as a set of top-level definitions because it can't be a math object because of usual paradoxes
  namespace MetaSet

  def hom (X Y) := X → Y

  def comp {X Y Z} (f : X → Y) (g : Y → Z) : X → Z := λ x => g (f x)

  def id (X) : X → X := λ x => x

  @[simp]
  def id_comp {X Y} : ∀ (f : X → Y), comp (id X) f = f := λ _ => rfl

  @[simp]
  def comp_id {X Y} : ∀ (f : X → Y), comp f (id Y) = f := λ _ => rfl
  
  def assoc {X Y Z W} : ∀ (f : X → Y) (g : Y → Z) (h : Z → W), 
      comp (comp f g) h = comp f (comp g h) := λ _ _ _ => rfl

  end MetaSet

end
end Category.Instances