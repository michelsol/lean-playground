import Playground.Algebra.Monoid
namespace Algebra
section
  variable {X} (data : AddZeroMulOne X)
  local infixl:65 " + " => data.addZero.op
  local infixl:70 " * " => data.mulOne.op
  local notation:max "𝟬" => data.addZero.identity

  namespace AddZeroMulOne

  class IsSemiring : Prop where
    addZero_isCommMonoid : data.addZero.IsCommMonoid
    mulOne_isMonoid : data.mulOne.IsMonoid
    mul_add : ∀ x y z : X, x * (y + z) = x * y + x * z
    add_mul : ∀ x y z : X, (x + y) * z = x * z + y * z
    mul_zero : ∀ x : X, x * 𝟬 = 𝟬
    zero_mul : ∀ x : X, 𝟬 * x = 𝟬
  export IsSemiring (addZero_isCommMonoid mulOne_isMonoid mul_add add_mul mul_zero zero_mul)
  instance [data.IsSemiring] : data.addZero.IsCommMonoid := addZero_isCommMonoid
  instance [data.IsSemiring] : data.mulOne.IsMonoid := mulOne_isMonoid

  class IsCommSemiring extends data.IsSemiring, data.mulOne.IsComm : Prop where
  instance [data.IsCommSemiring] : data.mulOne.IsCommMonoid := {}

  end AddZeroMulOne
end
section
  variable {X Y} {src : AddZeroMulOne X} {dst : AddZeroMulOne Y}
  namespace AddZeroMulOne.Function
  class IsSemiringMorphism [src.IsSemiring] [dst.IsSemiring] (f : Function src dst) : Prop where
    addZero_morphism : f.toAddZero.IsMonoidMorphism
    mulOne_morphism : f.toMulOne.IsMonoidMorphism
  end AddZeroMulOne.Function
end
end Algebra