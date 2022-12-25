import Playground.Algebra.Semiring
import Playground.Algebra.Group
namespace Algebra
section
  variable {X} (data : AddZeroNegMulOne X)
  namespace AddZeroNegMulOne

  class IsRing extends data.IsSemiring : Prop where
    addZeroNeg_isSymmetric : data.toAddZeroNeg.IsSymmetric
  instance [IsRing data] : data.toAddZeroNeg.IsSymmetric  := IsRing.addZeroNeg_isSymmetric
  instance [IsRing data] : data.IsSemiring := inferInstance
  instance [IsRing data] : data.toAddZeroNeg.IsCommGroup := {}

  class IsCommRing extends data.IsRing, data.toMulOne.IsComm : Prop where
  instance [data.IsCommRing] : data.toMulOne.IsCommMonoid := {}

  end AddZeroNegMulOne
end
section
  variable {X Y} {src : AddZeroNegMulOne X} {dst : AddZeroNegMulOne Y}
  namespace AddZeroNegMulOne.Function
  class IsRingMorphism [src.IsRing] [dst.IsRing] (f : Function src dst)  
  extends f.toAddZeroMulOne.IsSemiringMorphism : Prop
  end AddZeroNegMulOne.Function
end
end Algebra