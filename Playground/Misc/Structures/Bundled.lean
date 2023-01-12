namespace Algebra
section
  section
    structure Carrier.{u} where carrier : Type u
    export Carrier (carrier)
    structure BinOp extends Carrier where op : carrier → carrier → carrier
    structure Identity extends Carrier where identity : carrier
    structure Sym extends Carrier where sym : carrier → carrier
    structure Zero extends Carrier where zero : carrier
    structure Neg extends Carrier where neg : carrier → carrier
    structure One extends Carrier where one : carrier
    structure Inv extends Carrier where inv : carrier → carrier

    structure BinOpId extends BinOp, Identity
    structure BinOpIdSym extends BinOpId, Sym

    structure FunBinOp where
      src : BinOp
      dst : BinOp
      map : src.carrier → dst.carrier
    instance : CoeFun FunBinOp (λ f => f.src.carrier → f.dst.carrier) where coe f := f.map
    structure FunBinOpId where
      src : BinOpId
      dst : BinOpId
      map : src.carrier → dst.carrier
    instance : CoeFun FunBinOpId (λ f => f.src.carrier → f.dst.carrier) where coe f := f.map
    structure FunBinOpIdSym where
      src : BinOpIdSym
      dst : BinOpIdSym
      map : src.carrier → dst.carrier
    instance : CoeFun FunBinOpIdSym (λ f => f.src.carrier → f.dst.carrier) where coe f := f.map
    
    -- scoped infixl:70 " ⋆ " => BinOp.op _
    -- scoped notation:max "𝟙" => Identity.identity _
    -- scoped postfix:max "⁻ⁱ" => Sym.sym _
    -- scoped notation:max "𝟬" => Zero.zero
    -- scoped prefix:max "-" => Neg.neg
    -- scoped notation:max "𝟭" => One.one
    -- scoped postfix:max "⁻¹" => Inv.inv

  end

  section
    variable (X : BinOp)
    local infixl:70 " ⋆ " => BinOp.op X

    class Comm : Prop where
      comm : ∀ x y : X.carrier, x ⋆ y = y ⋆ x
    export Comm (comm)

    #check comm
  end

  #exit

  class Comm (X : BinOp) : Prop where
    comm : ∀ x y : X.carrier, x ⋆ y = y ⋆ x
  export Comm (comm)
  class AddComm (X) [Add X] extends Comm { carrier := X, op := Add.add } : Prop
  class MulComm (X) [Mul X] extends Comm { carrier := X, op := Mul.mul } : Prop

  class Semigroup (X : BinOp) : Prop where
    assoc : ∀ x y z : X.carrier, (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z)
  export Semigroup (assoc)

  class CommSemigroup (X : BinOp) extends Semigroup X, Comm X : Prop

  class Unital (X : BinOpId) : Prop where
    id_op : ∀ x : X.carrier,  (Identity.identity X.toIdentity) ⋆ x = x
    op_id : ∀ x : X.carrier, x ⋆ 𝟙 = x
  export Unital (id_op op_id)
  attribute [simp] id_op op_id


  class Monoid (X : BinOpId) extends Semigroup X.toBinOp, Unital X : Prop
  class AddMonoid (X) [Add X] [Inhabited X] extends Monoid { carrier := X, op := Add.add, identity := default } : Prop
  instance : AddMonoid Nat where
    assoc := Nat.add_assoc
    id_op := Nat.zero_add
    op_id := Nat.add_zero 

  class CommMonoid (X : BinOpId) extends Monoid X, Comm X.toBinOp : Prop

  class Symmetric (X : BinOpIdSym) : Prop where
    op_sym : ∀ x, x ⋆ x⁻ⁱ = 𝟙
    sym_op : ∀ x, x⁻ⁱ ⋆ x = 𝟙
  export Symmetric (op_sym sym_op)
  attribute [simp] op_sym sym_op

  class Group (X : BinOpIdSym) extends Monoid X.toBinOpId, Symmetric X : Prop

  class CommGroup (X : BinOpIdSym) extends Group X, Comm X.toBinOp : Prop

  class BinOp.Morphism (X Y : BinOp) (f : X.carrier → Y.carrier) : Prop where
    op_law : ∀ x y : X.carrier, 
      -- sorry = 0
      (x : X.carrier) ⋆ x = x
      -- f (x ⋆ y) = f x ⋆ f y

end
end Algebra