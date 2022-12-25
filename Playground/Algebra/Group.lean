import Playground.Algebra.Monoid
namespace Algebra
section
  variable {X} (data : OpIdSym X)
  local infixl:70 " ⋆ " => data.op
  local notation:max "𝟙" => data.identity
  local postfix:max "⁻ⁱ" => data.sym

  namespace OpIdSym
  class IsSymmetric : Prop where
    op_sym : ∀ x : X, x ⋆ x⁻ⁱ = 𝟙
    sym_op : ∀ x : X, x⁻ⁱ ⋆ x = 𝟙
  export IsSymmetric (op_sym sym_op)
  attribute [simp] op_sym sym_op
  class IsGroup extends OpId.IsMonoid data.toOpId, IsSymmetric data  : Prop
  class IsCommGroup extends IsGroup data, Op.IsComm data.toOp : Prop
  end OpIdSym
end
section
  variable {X Y} {src : OpIdSym X} {dst : OpIdSym Y}
  namespace OpIdSym.Function
  class IsGroupMorphism [src.IsGroup] [dst.IsGroup] (f : Function src dst)
  extends f.toOpId.IsMonoidMorphism : Prop
  end OpIdSym.Function
end
end Algebra