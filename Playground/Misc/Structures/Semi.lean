namespace Algebra

section
  universe u
  variable (X : Type u)
  structure Op where op : X → X → X
end
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
  variable {X Y}
  variable {src : Op X} {dst : Op Y}
  local infixl:70 " ⋆ " => src.op
  local infixl:70 " ⋆ " => dst.op
  namespace Op
  structure Function (src : Op X) (dst : Op Y) where map : X → Y
  namespace Function
  instance : CoeFun (Function src dst) (λ _ => X → Y) where coe f := f.map
  class IsSemigroupMorphism [src.IsSemigroup] [dst.IsSemigroup] (f : Function src dst) : Prop where
    op_law : ∀ x y, f (x ⋆ y) = f x ⋆ f y
  attribute [simp] IsSemigroupMorphism.op_law
  end Function
  end Op
end

section
  universe u
  variable (X : Type u)
  structure Identity where identity : X
  class Zero where zero : X
  class One where one : X
  structure OpId extends Op X, Identity X
  attribute [reducible] OpId.toOp OpId.toIdentity
end
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
  class IsAddMonoid (X) [Add X] [Zero X] extends IsMonoid { op := Add.add, identity := (Zero.zero : X) } : Prop
  class IsCommMonoid extends data.IsMonoid, data.IsComm : Prop
  end OpId
end
section
  variable {X Y}
  variable {src : OpId X} {dst : OpId Y}
  local infixl:70 " ⋆ " => src.op
  local infixl:70 " ⋆ " => dst.op
  local notation:max "𝟙" => src.identity
  local notation:max "𝟙" => dst.identity
  namespace OpId
  structure Function (src : OpId X) (dst : OpId Y) where map : X → Y
  namespace Function
  instance : CoeFun (Function src dst) (λ _ => X → Y) where coe f := f.map
  abbrev toOp (f : Function src dst) : Op.Function src.toOp dst.toOp := ⟨f.1⟩
  class IsMonoidMorphism [src.IsMonoid] [dst.IsMonoid] (f : Function src dst)
  extends f.toOp.IsSemigroupMorphism : Prop where
    id_law : f 𝟙 = (𝟙 : Y)
  attribute [simp] IsMonoidMorphism.id_law
  end Function
  end OpId
end

end Algebra