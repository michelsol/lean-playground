import Playground.Algebra.Semigroup
namespace Algebra
section
  variable {X} (data : OpId X)
  local infixl:70 " ⋆ " => data.op
  local notation:max "𝟙" => data.identity
  namespace OpId
  class IsUnital : Prop where
    id_op : ∀ x : X, 𝟙 ⋆ x = x
    op_id : ∀ x : X, x ⋆ 𝟙 = x
  export IsUnital (id_op op_id)
  attribute [simp] id_op op_id
  class IsMonoid extends data.IsSemigroup, data.IsUnital : Prop
  class IsCommMonoid extends data.IsMonoid, data.IsComm : Prop
  end OpId
end
section
  variable {X Y} {src : OpId X} {dst : OpId Y}
  local notation:max "𝟙" => src.identity
  local notation:max "𝟙" => dst.identity
  namespace OpId.Function
  class IsMonoidMorphism [src.IsMonoid] [dst.IsMonoid] (f : Function src dst)
  extends f.toOp.IsSemigroupMorphism : Prop where
    id_law : f 𝟙 = (𝟙 : Y)
  attribute [simp] IsMonoidMorphism.id_law
  end OpId.Function
end
end Algebra