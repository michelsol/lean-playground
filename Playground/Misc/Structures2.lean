
namespace Algebra


section
  class Carrier_Of (α : Type u) where
    carrier_of : α → Type v

  @[app_unexpander Carrier_Of.carrier_of] def unexpand_carrier_of : Lean.PrettyPrinter.Unexpander
  | `($(_) $a) => `(↑$a)
  | _                => throw ()

  instance (α) [Carrier_Of α] : CoeSort α (Type v) := ⟨Carrier_Of.carrier_of⟩
end


section
  variable (α) [Carrier_Of α]

  class Binop_Of where binop_of {X : α} : X → X → X
  class Identity_Of where id_of {X : α} : X
  class Sym_Of where sym_of {X : α} : X → X
  class Add_Of where add_of {X : α} : X → X → X
  class Zero_Of where zero_of {X : α} : X
  class Neg_Of where neg_of {X : α} : X → X
  class Mul_Of where mul_of {X : α} : X → X → X
  class One_Of where one_of {X : α} : X
  class Inv_Of where inv_of {X : α} : X → X
end


section

  structure Carrier.{u} where
    carrier : Type u

  namespace Carrier
    instance : Carrier_Of Carrier := ⟨λ X => X.carrier⟩
  end Carrier

  structure Binop extends Carrier where
    binop : carrier → carrier → carrier

  namespace Binop
    instance : Carrier_Of Binop := ⟨λ X => X.carrier⟩
    instance : Binop_Of Binop := ⟨λ {X} => X.binop⟩
  end Binop

  structure BinopId extends Binop where
    identity : carrier

  namespace BinopId
    instance : Carrier_Of BinopId := ⟨λ X => X.carrier⟩
    instance : Identity_Of BinopId := ⟨λ {X} => X.identity⟩
    instance : Binop_Of BinopId := ⟨λ {X} => X.binop⟩
    instance : Coe BinopId Binop := ⟨λ X => X.toBinop⟩
  end BinopId

  structure BinopIdSym extends BinopId where
    sym : carrier → carrier

  namespace BinopIdSym
    instance : Carrier_Of BinopIdSym := ⟨λ X => X.carrier⟩
    instance : Identity_Of BinopIdSym := ⟨λ {X} => X.identity⟩
    instance : Binop_Of BinopIdSym := ⟨λ {X} => X.binop⟩
    instance : Sym_Of BinopIdSym := ⟨λ {X} => X.sym⟩
    instance : Coe BinopIdSym BinopId := ⟨λ X => X.toBinopId⟩
    instance : Coe BinopIdSym Binop := ⟨λ X => X.toBinop⟩
  end BinopIdSym

  structure AddZeroMulOne extends Carrier where
    add : carrier → carrier → carrier
    zero : carrier
    mul : carrier → carrier → carrier
    one : carrier

  namespace AddZeroMulOne
    instance : Carrier_Of AddZeroMulOne := ⟨λ X => X.carrier⟩
    instance : Add_Of AddZeroMulOne := ⟨λ {X} => X.add⟩
    instance : Zero_Of AddZeroMulOne := ⟨λ {X} => X.zero⟩
    instance : Mul_Of AddZeroMulOne := ⟨λ {X} => X.mul⟩
    instance : One_Of AddZeroMulOne := ⟨λ {X} => X.one⟩
    def toAddZero (X : AddZeroMulOne) : BinopId := {
      carrier := X
      binop := X.add
      identity := X.zero
    }
    instance : Coe AddZeroMulOne BinopId := ⟨λ X => X.toAddZero⟩
    def toMulOne (X : AddZeroMulOne) : BinopId := {
      carrier := X
      binop := X.mul
      identity := X.one
    }
  end AddZeroMulOne

  structure AddZeroNegMulOne extends AddZeroMulOne where
    neg : carrier → carrier

  namespace AddZeroNegMulOne
    instance : Carrier_Of AddZeroNegMulOne := ⟨λ X => X.carrier⟩
    instance : Add_Of AddZeroNegMulOne := ⟨λ {X} => X.add⟩
    instance : Zero_Of AddZeroNegMulOne := ⟨λ {X} => X.zero⟩
    instance : Neg_Of AddZeroNegMulOne := ⟨λ {X} => X.neg⟩
    instance : Mul_Of AddZeroNegMulOne := ⟨λ {X} => X.mul⟩
    instance : One_Of AddZeroNegMulOne := ⟨λ {X} => X.one⟩
    instance : Coe AddZeroNegMulOne AddZeroMulOne := ⟨λ X => X.toAddZeroMulOne⟩
    def toAddZeroNeg (X : AddZeroNegMulOne) : BinopIdSym := {
      carrier := X
      binop := X.add
      identity := X.zero
      sym := X.neg
    }
    instance : Coe AddZeroNegMulOne BinopIdSym := ⟨λ X => X.toAddZeroNeg⟩
  end AddZeroNegMulOne

end




section
  local infixl:70 " ⋆ " => Binop_Of.binop_of
  local notation:max "𝟙" => Identity_Of.id_of
  local postfix:max "⁻ⁱ" => Sym_Of.sym_of
  -- local infixl:65 " + " => Add_Of.add_of
  local instance (X : α) [Carrier_Of α] [Add_Of α] : Add X where add := Add_Of.add_of
  local notation:max "𝟬" => Zero_Of.zero_of
  local prefix:max "-" => Neg_Of.neg_of
  -- local infixl:70 " * " => Mul_Of.mul_of
  local instance (X : α) [Carrier_Of α] [Mul_Of α] : Mul X where mul := Mul_Of.mul_of
  local notation:max "𝟭" => One_Of.one_of
  local postfix:max "⁻¹" => Inv_Of.inv_of


  class Comm (X : Binop) : Prop where
    comm : ∀ x y : X, x ⋆ y = y ⋆ x
  export Comm (comm)

  class Semigroup (X : Binop) : Prop where
    assoc : ∀ x y z : X, (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z)
  export Semigroup (assoc)

  class CommSemigroup (X : Binop) extends Semigroup X, Comm X : Prop

  class Unital (X : BinopId) : Prop where
    id_op : ∀ x : X, 𝟙 ⋆ x = x
    op_id : ∀ x : X, x ⋆ 𝟙 = x
  export Unital (id_op op_id)
  attribute [simp] id_op op_id

  class Monoid (X : BinopId) extends Semigroup X, Unital X : Prop

  class CommMonoid (X : BinopId) extends Monoid X, Comm X : Prop

  class Symmetric (X : BinopIdSym) : Prop where
    op_sym : ∀ x : X, x ⋆ x⁻ⁱ = 𝟙
    sym_op : ∀ x : X, x⁻ⁱ ⋆ x = 𝟙
  export Symmetric (op_sym sym_op)
  attribute [simp] op_sym sym_op

  class Group (X : BinopIdSym) extends Monoid X, Symmetric X : Prop

  class CommGroup (X : BinopIdSym) extends Group X, Comm X : Prop

  class Binop.Morphism {X Y : Binop} (f : X → Y) : Prop where
    op_law : ∀ x y, f (x ⋆ y) = f x ⋆ f y

  class Unital.Morphism {X Y} [Unital X] [Unital Y] (f : X → Y) extends Binop.Morphism f : Prop where
    op_id : f 𝟙 = 𝟙

  class Monoid.Morphism {X Y} [Monoid X] [Monoid Y] (f : X → Y) extends Unital.Morphism f : Prop

  class Group.Morphism {X Y} [Group X] [Group Y] (f : X → Y) extends Monoid.Morphism f : Prop


  class Semiring (X : AddZeroMulOne) : Prop where
    comm_monoid_add_zero : CommMonoid X.toAddZero
    monoid_mul_one : Monoid X.toMulOne
    mul_add : ∀ x y z : X, x * (y + z) = x * y + x * z
    add_mul : ∀ x y z : X, (x + y) * z = x * z + y * z
    mul_zero : ∀ x : X, x * 𝟬 = 𝟬
    zero_mul : ∀ x : X, 𝟬 * x = 𝟬
  instance [Semiring X] : CommMonoid X := Semiring.comm_monoid_add_zero
  instance [Semiring X] : Monoid X.toMulOne := Semiring.monoid_mul_one

  class CommSemiring (X : AddZeroMulOne) extends Semiring X, Comm X.toMulOne : Prop where
  instance [CommSemiring X] : CommMonoid X.toMulOne := {}

  class Ring (X : AddZeroNegMulOne) extends Semiring X : Prop where
    sym_add_zero_neg : Symmetric X
  instance [Ring X] : Symmetric X := Ring.sym_add_zero_neg
  local instance [Ring X] : CommMonoid X.toAddZeroNeg := inferInstanceAs $ CommMonoid X in
  instance [Ring X] : CommGroup X := {}

  class CommRing (X : AddZeroNegMulOne) extends Ring X, Comm X.toMulOne : Prop where
  instance [CommRing X] : CommSemiring X := {}

  class Ring.Morphism {X Y} [Ring X] [Ring Y] (f : X → Y) : Prop where
    add_morphism : @Monoid.Morphism X.toAddZero Y.toAddZero _ _ f
    mul_morphism : @Monoid.Morphism X.toMulOne Y.toMulOne _ _ f


  def kernel {X Y} [Unital X] [Unital Y] (f : X → Y) [Unital.Morphism f] : X → Prop
    := λ x => f x = 𝟙


  example [CommGroup X] : ∀ x y : X, x ⋆ y = y ⋆ x := comm
  example [CommGroup X] : ∀ x y z : X, (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z) := assoc
  example [CommMonoid X] : ∀ x : X, x ⋆ 𝟙 = x := by simp
  example [CommGroup X] : ∀ x : X, x ⋆ 𝟙 = x := op_id
  example [CommGroup X] : ∀ x : X, x ⋆ 𝟙 = x := 
  show ∀ x : (X : BinopId), x ⋆ 𝟙 = x from
  by simp
  example [CommGroup X] : ∀ x : X, x ⋆ x⁻ⁱ = 𝟙 := by simp
  example [CommRing X] : ∀ x : X, x + 𝟬 = x := 
  let X := X.toAddZero
  show ∀ x : X, x ⋆ 𝟙 = x from
  by simp

  example {X Y : Binop} (f : X → Y) [Binop.Morphism f] : ∀ x y, f (x ⋆ y) = f x ⋆ f y := Binop.Morphism.op_law
  example {X Y Z : Binop} (f : X → Y) [fi : Binop.Morphism f] (g : Y → Z) [gi : Binop.Morphism g] 
  : Binop.Morphism (g ∘ f) where
    op_law x y := show g (f (x ⋆ y)) = g (f x) ⋆ g (f y) from fi.op_law .. ▸ gi.op_law .. ▸ rfl

  example {X Y} [Ring X] [Ring Y] (f : X → Y) [Ring.Morphism f] : f 𝟭 = 𝟭 
    := Ring.Morphism.mul_morphism.op_id

  example {X} [Ring X] : Unital X := inferInstance

  example {X Y} [Ring X] [Ring Y] (f : X → Y) [@Unital.Morphism X Y _ _ f] : (@kernel X Y _ _ f) (𝟬 : X) := 
    @Unital.Morphism.op_id X Y _ _ f _

end



end Algebra
