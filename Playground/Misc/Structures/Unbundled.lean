namespace Algebra

section
  universe u
  variable (X : Type u)
  class Op where op : X → X → X
  scoped infixl:70 " ⋆ " => Op.op
end
section
  variable {X} (data : Op X)
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
  class Identity where identity : X
  scoped notation:max "𝟙" => Identity.identity
  class Zero where zero : X
  scoped notation:max "𝟬" => Zero.zero
  class One where one : X
  scoped notation:max "𝟭" => One.one
  class OpId extends Op X, Identity X
  attribute [reducible] OpId.toOp OpId.toIdentity
end
section
  variable {X} (data : OpId X)
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
  namespace OpId
  structure Function (src : OpId X) (dst : OpId Y) where map : X → Y
  namespace Function
  instance : CoeFun (Function src dst) (λ _ => X → Y) where coe f := f.map
  abbrev toOp (f : Function src dst) : Op.Function src.toOp dst.toOp := ⟨f.1⟩
  class IsMonoidMorphism [src.IsMonoid] [dst.IsMonoid] (f : Function src dst)
  extends f.toOp.IsSemigroupMorphism : Prop where
    id_law : f 𝟙 = 𝟙
  attribute [simp] IsMonoidMorphism.id_law
  end Function
  end OpId
end

section
  universe u
  variable (X : Type u)
  class Sym where sym : X → X
  scoped postfix:max "⁻ⁱ" => Sym.sym
  class Neg where neg : X → X
  scoped prefix:max "-" => Neg.neg
  class Inv where inv : X → X
  scoped postfix:max "⁻¹" => Inv.inv
  class OpIdSym extends OpId X, Sym X
  attribute [reducible] OpIdSym.toOpId OpIdSym.toSym
end
section
  variable {X} (data : OpIdSym X)
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
  class AddZeroMulOne extends Add X, Zero X, Mul X, One X
  attribute [reducible] AddZeroMulOne.toAdd AddZeroMulOne.toZero AddZeroMulOne.toMul AddZeroMulOne.toOne
end
section
  variable {X} (data : AddZeroMulOne X)
  namespace AddZeroMulOne
  abbrev toAddZero : OpId X := { op := data.add, identity := data.zero }
  abbrev toMulOne : OpId X := { op := data.mul, identity := data.one }

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

  class IsCommSemiring extends data.IsSemiring, data.toMulOne.IsComm : Prop where
  instance [data.IsCommSemiring] : data.toMulOne.IsCommMonoid := {}

  end AddZeroMulOne
end
section
  variable {X Y}
  variable {src : AddZeroMulOne X} {dst : AddZeroMulOne Y}
  namespace AddZeroMulOne
  structure Function (src : AddZeroMulOne X) (dst : AddZeroMulOne Y) where map : X → Y
  namespace Function
  instance : CoeFun (Function src dst) (λ _ => X → Y) where coe f := f.map
  abbrev toAddZero (f : Function src dst) : OpId.Function src.toAddZero dst.toAddZero := ⟨f.1⟩
  abbrev toMulOne (f : Function src dst) : OpId.Function src.toMulOne dst.toMulOne := ⟨f.1⟩
  class IsSemiringMorphism [src.IsSemiring] [dst.IsSemiring] (f : Function src dst) : Prop where
    addZero_Morphism : f.toAddZero.IsMonoidMorphism
    mulOne_Morphism : f.toMulOne.IsMonoidMorphism
  end Function
  end AddZeroMulOne
end

section
  universe u
  variable (X : Type u)
  class AddZeroNegMulOne extends AddZeroMulOne X, Neg X
  attribute [reducible] AddZeroNegMulOne.toAddZeroMulOne AddZeroNegMulOne.toNeg
end
section
  variable {X} (data : AddZeroNegMulOne X)
  namespace AddZeroNegMulOne
  abbrev toAddZero : OpId X := data.toAddZeroMulOne.toAddZero
  abbrev toMulOne : OpId X := data.toAddZeroMulOne.toMulOne
  abbrev toAddZeroNeg : OpIdSym X := { toOpId := data.toAddZero, sym := data.neg }

  class IsRing extends data.IsSemiring : Prop where
    addZeroNeg_IsSymmetric : data.toAddZeroNeg.IsSymmetric
  instance [IsRing data] : data.toAddZeroNeg.IsSymmetric  := IsRing.addZeroNeg_IsSymmetric
  instance [IsRing data] : data.IsSemiring := inferInstance
  instance [IsRing data] : data.toAddZeroNeg.IsCommGroup := {
    toIsComm := OpId.IsCommMonoid.toIsComm -- why cant it infer it?
  }
  end AddZeroNegMulOne
end
section
  variable {X Y}
  variable {src : AddZeroNegMulOne X} {dst : AddZeroNegMulOne Y}
  namespace AddZeroNegMulOne
  structure Function (src : AddZeroNegMulOne X) (dst : AddZeroNegMulOne Y) where map : X → Y
  namespace Function
  instance : CoeFun (Function src dst) (λ _ => X → Y) where coe f := f.map
  abbrev toAddZeroMulOne (f : Function src dst) : AddZeroMulOne.Function src.toAddZeroMulOne dst.toAddZeroMulOne := ⟨f.1⟩
  abbrev toAddZeroNeg (f : Function src dst) : OpIdSym.Function src.toAddZeroNeg dst.toAddZeroNeg := ⟨f.1⟩
  abbrev toAddZero (f : Function src dst) : OpId.Function src.toAddZero dst.toAddZero := f.toAddZeroMulOne.toAddZero
  abbrev toMulOne (f : Function src dst) : OpId.Function src.toMulOne dst.toMulOne := f.toAddZeroMulOne.toMulOne
  class IsRingMorphism [src.IsRing] [dst.IsRing] (f : Function src dst)  
  extends f.toAddZeroMulOne.IsSemiringMorphism : Prop
  end Function
  end AddZeroNegMulOne
end




example (X) (data : OpIdSym X) [data.IsCommGroup] : ∀ x y : X, x ⋆ y = y ⋆ x := Op.comm
example (X) (data : OpIdSym X) [data.IsCommGroup] : ∀ x : X, x ⋆ 𝟙 = x := by simp
example (X) (data : OpIdSym X) [data.IsCommGroup] : ∀ x : X, x ⋆ x⁻ⁱ = 𝟙 := by simp
example (X) (data : AddZeroMulOne X) [data.IsSemiring] : ∀ x : X, x + 𝟬 = x := 
  let _ := data.toAddZero
  show ∀ x : X, x ⋆ 𝟙 = x from
  by simp


def kernel {X Y} {src : OpId X} {dst : OpId Y} [src.IsMonoid] [dst.IsMonoid] (f : OpId.Function src dst) : X → Prop
  := λ x => f x = 𝟙

example {X Y} {src : AddZeroNegMulOne X} {dst : AddZeroNegMulOne Y} [src.IsRing] [dst.IsRing] 
  (f : AddZeroNegMulOne.Function src dst) (h : f.IsRingMorphism)
  : kernel f.toAddZero 𝟬 := h.addZero_Morphism.id_law
example {X Y} {src : AddZeroNegMulOne X} {dst : AddZeroNegMulOne Y} [src.IsRing] [dst.IsRing] 
  (f : AddZeroNegMulOne.Function src dst) (h : f.IsRingMorphism)
  : kernel f.toMulOne 𝟭 := h.mulOne_Morphism.id_law



end Algebra