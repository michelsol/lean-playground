namespace Algebra

class Binop (α : Type u) where
  binop : α → α → α

class Identity (α : Type u) where 
  identity : α

class Inv (α : Type u) where
  inv : α → α

section
local infixl:65 " * " => Binop.binop
local notation:max "𝟙" => Identity.identity
local postfix:100 "⁻¹" => Inv.inv

variable (α : Type u) [Binop α] [Identity α] [Inv α]

class Comm where
  comm : ∀ x y : α, x * y = y * x
export Comm (comm)

class Semigroup where
  assoc : ∀ x y z : α, (x * y) * z = x * (y * z)
export Semigroup (assoc)

class CommSemigroup extends Semigroup α, Comm α

class Unital where
  id_op : ∀ x : α, 𝟙 * x = x
  op_id : ∀ x : α, x * 𝟙 = x
@[simp] def id_op := @Unital.id_op
@[simp] def op_id := @Unital.op_id

class Monoid extends Semigroup α, Unital α

class CommMonoid extends Monoid α, Comm α

class Symmetric where
  op_inv : ∀ x : α, x * x⁻¹ = 𝟙
  inv_op : ∀ x : α, x⁻¹ * x = 𝟙
@[simp] def op_inv := @Symmetric.op_inv
@[simp] def inv_op := @Symmetric.inv_op

class Group extends Monoid α, Symmetric α

class CommGroup extends Group α, Comm α

end

section
local infixl:65 " + " => Binop.binop
local notation:max "𝟘" => Identity.identity
local prefix:100 "-" => Inv.inv

variable (α : Type u) [Binop α] [Identity α] [Inv α]

example [CommGroup α] : ∀ x y : α, x + y = y + x := comm
example [CommGroup α] : ∀ x y z : α, (x + y) + z = x + (y + z) := assoc
example [CommGroup α] : ∀ x : α, x + 𝟘 = x := by simp
example [CommGroup α] : ∀ x : α, x + -x = 𝟘 := by simp
end



class Zero (α : Type u) where 
  zero : α
class One (α : Type u) where 
  One : α


section Rings

variable (α : Type u)  
variable [Add α] [Zero α]
-- variable [Mul α] [One α]

local instance : Binop α := ⟨Add.add⟩ in
local instance : Identity α := ⟨Zero.zero⟩ in
class AddMonoid extends Monoid α

example [i : AddMonoid α] : ∀ x : α, x + Zero.zero = x := 
  let this := i.toMonoid
  sorry

end Rings


end Algebra