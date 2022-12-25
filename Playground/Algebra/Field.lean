import Playground.Algebra.Ring
namespace Algebra
section
  variable {X} (data : AddZeroNegMulOneInv X)
  local infixl:65 " + " => data.addZero.op
  local notation:max "𝟬" => data.addZero.identity
  local prefix:max "-" => data.neg
  local infixl:70 " * " => data.mulOne.op
  local notation:max "𝟭" => data.mulOne.identity
  local postfix:max "⁻¹" => data.inv

  namespace AddZeroNegMulOneInv

  class IsField extends data.IsCommRing : Prop where
    zero_ne_one : 𝟬 ≠ 𝟭
    mulOneInv_isSymmetric : data.toMulOneInv.IsSymmetric

  instance [IsField data] : data.toMulOneInv.IsSymmetric  := IsField.mulOneInv_isSymmetric
  instance [IsField data] : data.toMulOneInv.IsCommGroup  := {}
  example [IsField data] : data.toAddZeroNeg.IsCommGroup := inferInstance

  end AddZeroNegMulOneInv
end
section
  variable {X Y} {src : AddZeroNegMulOneInv X} {dst : AddZeroNegMulOneInv Y}
  namespace AddZeroNegMulOneInv.Function
  class IsFieldMorphism [src.IsField] [dst.IsField] (f : Function src dst)  
  extends f.toAddZeroNegMulOne.IsRingMorphism : Prop
  end AddZeroNegMulOneInv.Function
end
end Algebra