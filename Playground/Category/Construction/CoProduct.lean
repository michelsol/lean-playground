import Playground.Category.Functor.Basic

namespace Category.Construction
section
  -- structure CoProduct {C} [Category C] {I} (X : asDiscrete I ⥤ C) where
  --   object : C
  --   morphism : (i : _) → X i ⟶ object
  --   property : ∀ {O} (f : (i : _) → X i ⟶ O), ∃! α : object ⟶ O, ∀ i, morphism i ≫ α = f i

  -- class CoProducts (C) [Category C] where
  --   coProductOf {I} (X : asDiscrete I ⥤ C) : CoProduct X
  -- export CoProducts (coProductOf)
end
end Category.Construction