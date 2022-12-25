import Playground.Category.Functor.Universal
import Playground.Category.Instances.Discrete

section
  namespace Category.Functor.Limit
  def Product.Diagram.Shape (I : Type _) := I

  instance {I} : Category (Product.Diagram.Shape I) := Instances.discreteCategoryOf I

  abbrev Product.Diagram (C) [Category C] (I : Type _) := Diagram.Shape I ⥤ C

  def Product {C} [Category C] {I} (X : Product.Diagram C I) := Limit X
  end Category.Functor.Limit
end