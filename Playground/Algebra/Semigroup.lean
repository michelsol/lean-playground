import Playground.Algebra.Structures
namespace Algebra
section
  variable {X} (data : Op X)
  local infixl:70 " ⋆ " => data.op
  namespace Op
  class IsComm : Prop where comm : ∀ x y : X, x ⋆ y = y ⋆ x
  export IsComm (comm)
  class IsSemigroup : Prop where assoc : ∀ x y z : X, (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z)
  export IsSemigroup (assoc)
  class IsCommSemigroup extends data.IsSemigroup, data.IsComm : Prop
  end Op
end
section
  variable {X Y} {src : Op X} {dst : Op Y}
  local infixl:70 " ⋆ " => src.op
  local infixl:70 " ⋆ " => dst.op
  namespace Op.Function
  class IsSemigroupMorphism [src.IsSemigroup] [dst.IsSemigroup] (f : Function src dst) : Prop where
    op_law : ∀ x y, f (x ⋆ y) = f x ⋆ f y
  attribute [simp] IsSemigroupMorphism.op_law
  end Op.Function
end
end Algebra