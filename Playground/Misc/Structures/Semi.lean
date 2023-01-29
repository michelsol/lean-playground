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

section
  universe u
  variable (X : Type u)
  structure Sym where sym : X → X
  structure OpIdSym extends OpId X, Sym X
  attribute [reducible] OpIdSym.toOpId OpIdSym.toSym
end
section
  variable {X} (data : OpIdSym X)
  local infixl:70 " ⋆ " => data.op
  local notation:max "𝟙" => data.identity
  local postfix:max "⁻ⁱ" => data.sym
  -- local prefix:max "-" => data.neg
  -- local postfix:max "⁻¹" => data.inv
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
  variable {X Y}
  variable {src : OpIdSym X} {dst : OpIdSym Y}
  namespace OpIdSym
  structure Function (src : OpIdSym X) (dst : OpIdSym Y) where map : X → Y
  namespace Function
  instance : CoeFun (Function src dst) (λ _ => X → Y) where coe f := f.map
  abbrev toOpId (f : Function src dst) : OpId.Function src.toOpId dst.toOpId := ⟨f.1⟩
  abbrev toOp (f : Function src dst) : Op.Function src.toOp dst.toOp := f.toOpId.toOp
  class IsGroupMorphism [src.IsGroup] [dst.IsGroup] (f : Function src dst)
  extends f.toOpId.IsMonoidMorphism : Prop
  end Function
  end OpIdSym
end


section
  universe u
  variable (X : Type u)
  structure AddZeroMulOne where
    toAddZero : OpId X
    toMulOne : OpId X
  attribute [reducible] AddZeroMulOne.toAddZero AddZeroMulOne.toMulOne
end
section
  variable {X} (data : AddZeroMulOne X)
  local infixl:65 " + " => data.toAddZero.op
  local infixl:70 " * " => data.toMulOne.op
  local notation:max "𝟬" => data.toAddZero.identity
  local notation:max "𝟭" => data.toMulOne.identity
  namespace AddZeroMulOne

  class IsSemiring : Prop where
    addZero_IsCommMonoid : data.toAddZero.IsCommMonoid
    mulOne_IsMonoid : data.toMulOne.IsMonoid
    mul_add : ∀ x y z : X, x * (y + z) = x * y + x * z
    add_mul : ∀ x y z : X, (x + y) * z = x * z + y * z
    mul_zero : ∀ x : X, x * 𝟬 = 𝟬
    zero_mul : ∀ x : X, 𝟬 * x = 𝟬
  export IsSemiring (addZero_IsCommMonoid mulOne_IsMonoid mul_add add_mul mul_zero zero_mul)
  instance [data.IsSemiring] : data.toAddZero.IsCommMonoid := addZero_IsCommMonoid
  instance [data.IsSemiring] : data.toMulOne.IsMonoid := mulOne_IsMonoid

  class IsCommSemiring extends data.IsSemiring, data.toMulOne.IsComm : Prop
  instance [data.IsCommSemiring] : data.toMulOne.IsCommMonoid := {}

  end AddZeroMulOne
end

section
  variable (X) (data : OpIdSym X)
  local infixl:70 " ⋆ " => data.op
  local notation:max "𝟙" => data.identity
  local postfix:max "⁻ⁱ" => data.sym
  example [data.IsCommGroup] (x : X) : x ⋆ 𝟙 = x := by simp
end

section
  variable (X) (data : AddZeroMulOne X)
  local infixl:65 " + " => data.toAddZero.op
  local infixl:70 " * " => data.toMulOne.op
  local notation:max "𝟬" => data.toAddZero.identity
  local notation:max "𝟭" => data.toMulOne.identity

  section
  variable (z : Nat) 
  local notation " 𝟮 " => z
  #check 𝟮
  end

  -- @[app_unexpander Op.op] def unexpand_1 : Lean.PrettyPrinter.Unexpander
  -- | `(Op.op $c $a $b) => `($a + $b)
  -- | _                => throw ()
  example [data.IsSemiring] (x : X) : x + 𝟬 = x := by
    show x + 𝟬 = x
    simp
  example [data.IsSemiring] (x : X) : x * 𝟭 = x := by simp
end

end Algebra