import Playground.Algebra.Field
namespace Algebra
section

  variable {K} {E} (X : ModuleData K E)
  local infixl:70 " • " => X.smul
  local infixl:65 " + " => X.vectors.op
  local notation:max "𝟬" => X.vectors.identity
  local prefix:max "-" => X.vectors.sym
  local infixl:65 " + " => X.scalars.addZero.op
  local notation:max "𝟬" => X.scalars.addZero.identity
  local prefix:max "-" => X.scalars.neg
  local infixl:70 " * " => X.scalars.mulOne.op
  local notation:max "𝟭" => X.scalars.mulOne.identity
  local postfix:max "⁻¹" => X.scalars.inv

  class IsVectorSpace : Prop where
    scalars_isField : X.scalars.IsField
    vectors_isCommGroup : X.vectors.IsCommGroup
    id_smul : ∀ (x : E), 𝟭 • x = x
    smul_smul : ∀ (α β : K) (x : E), α • (β • x) = (α * β) • x
    smul_add : ∀ (α : K) (x y : E), α • (x + y) = α • x + α • y
    add_smul : ∀ (α β : K) (x : E), (α + β) • x = α • x + β • x
  export IsVectorSpace (id_smul smul_smul smul_add add_smul)

  variable [IsVectorSpace X]
  instance : X.scalars.IsField := IsVectorSpace.scalars_isField
  instance : X.vectors.IsCommGroup := IsVectorSpace.vectors_isCommGroup

  example (α : K) : α • 𝟬 = (𝟬 : E) := 
    have : ∀ x y z : E, x + z = y + z → x = y :=
      λ x y z h =>
        have h : _  = _ := congrArg (λ t : E => t + -z) h
        by
        dsimp at h
        rw [Op.assoc, Op.assoc, OpIdSym.op_sym, OpId.op_id, OpId.op_id] at h
        exact h
    this (α • 𝟬) 𝟬 (α • 𝟬) $
    by
    rw [OpId.id_op, ←smul_add, OpId.id_op]

  -- example (α : K) (x : E) (h : α • x = 𝟬) (hα : α ≠ 𝟬) : x = 𝟬 :=
  --   by
  --   rw [←iX.id_smul x]
  --   have : X.scalars.toMulOneInv.IsGroup := inferInstance
  --   have : α⁻¹ * α = 𝟭 := this.sym_op α
  --   rw [←this]
  --   rw [←smul_smul]
  --   rw [h]
  --   sorry

end
end Algebra
