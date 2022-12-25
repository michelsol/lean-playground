namespace Algebra

section
  universe u
  variable (X : Type u)
  structure Op where op : X → X → X
end
section
  variable {X Y}
  namespace Op
  structure Function (src : Op X) (dst : Op Y) where map : X → Y
  namespace Function
  variable {src : Op X} {dst : Op Y}
  instance : CoeFun (Function src dst) (λ _ => X → Y) where coe f := f.map
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
  variable {X Y}
  variable {src : OpId X} {dst : OpId Y}
  namespace OpId
  structure Function (src : OpId X) (dst : OpId Y) where map : X → Y
  namespace Function
  instance : CoeFun (Function src dst) (λ _ => X → Y) where coe f := f.map
  abbrev toOp (f : Function src dst) : Op.Function src.toOp dst.toOp := ⟨f.1⟩
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
  variable {X Y}
  variable {src : OpIdSym X} {dst : OpIdSym Y}
  namespace OpIdSym
  structure Function (src : OpIdSym X) (dst : OpIdSym Y) where map : X → Y
  namespace Function
  instance : CoeFun (Function src dst) (λ _ => X → Y) where coe f := f.map
  abbrev toOpId (f : Function src dst) : OpId.Function src.toOpId dst.toOpId := ⟨f.1⟩
  abbrev toOp (f : Function src dst) : Op.Function src.toOp dst.toOp := f.toOpId.toOp
  end Function
  end OpIdSym
end

section
  universe u
  variable (X : Type u)
  structure AddZeroMulOne where
    addZero : OpId X
    mulOne : OpId X
  attribute [reducible] AddZeroMulOne.addZero AddZeroMulOne.mulOne
end
section
  variable {X Y}
  variable {src : AddZeroMulOne X} {dst : AddZeroMulOne Y}
  namespace AddZeroMulOne
  structure Function (src : AddZeroMulOne X) (dst : AddZeroMulOne Y) where map : X → Y
  namespace Function
  instance : CoeFun (Function src dst) (λ _ => X → Y) where coe f := f.map
  abbrev toAddZero (f : Function src dst) : OpId.Function src.addZero dst.addZero := ⟨f.1⟩
  abbrev toMulOne (f : Function src dst) : OpId.Function src.mulOne dst.mulOne := ⟨f.1⟩
  end Function
  end AddZeroMulOne
end

section
  universe u
  variable (X : Type u)
  structure AddZeroNegMulOne extends AddZeroMulOne X where
    neg : Sym X
  attribute [reducible] AddZeroNegMulOne.toAddZeroMulOne AddZeroNegMulOne.neg
end
section
  variable {X} (data : AddZeroNegMulOne X)
  namespace AddZeroNegMulOne
  abbrev toAddZero : OpId X := data.toAddZeroMulOne.addZero
  abbrev toMulOne : OpId X := data.toAddZeroMulOne.mulOne
  abbrev toAddZeroNeg : OpIdSym X := { toOpId := data.toAddZero, toSym := data.neg }
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
  abbrev toAddZero (f : Function src dst) := f.toAddZeroMulOne.toAddZero
  abbrev toMulOne (f : Function src dst) := f.toAddZeroMulOne.toMulOne
  end Function
  end AddZeroNegMulOne
end


section
  universe u
  variable (X : Type u)
  structure AddZeroNegMulOneInv extends AddZeroNegMulOne X where
    inv : Sym X
  attribute [reducible] AddZeroNegMulOneInv.toAddZeroNegMulOne AddZeroNegMulOneInv.inv
end
section
  variable {X} (data : AddZeroNegMulOneInv X)
  namespace AddZeroNegMulOneInv
  abbrev toAddZeroNeg : OpIdSym X := { toOpId := data.toAddZero, toSym := data.neg }
  abbrev toAddZero := data.toAddZeroMulOne.addZero
  abbrev toMulOneInv : OpIdSym X := { toOpId := data.toMulOne, toSym := data.inv }
  abbrev toMulOne := data.toAddZeroMulOne.mulOne
  end AddZeroNegMulOneInv
end
section
  variable {X Y}
  variable {src : AddZeroNegMulOneInv X} {dst : AddZeroNegMulOneInv Y}
  namespace AddZeroNegMulOneInv
  structure Function (src : AddZeroNegMulOneInv X) (dst : AddZeroNegMulOneInv Y) where map : X → Y
  namespace Function
  instance : CoeFun (Function src dst) (λ _ => X → Y) where coe f := f.map
  abbrev toAddZeroNegMulOne (f : Function src dst) : AddZeroNegMulOne.Function src.toAddZeroNegMulOne dst.toAddZeroNegMulOne := ⟨f.1⟩
  abbrev toAddZeroMulOne (f : Function src dst) : AddZeroMulOne.Function src.toAddZeroMulOne dst.toAddZeroMulOne := ⟨f.1⟩
  abbrev toAddZeroNeg (f : Function src dst) : OpIdSym.Function src.toAddZeroNeg dst.toAddZeroNeg := ⟨f.1⟩
  abbrev toAddZero (f : Function src dst) := f.toAddZeroMulOne.toAddZero
  abbrev toMulOneInv (f : Function src dst) : OpIdSym.Function src.toMulOneInv dst.toMulOneInv := ⟨f.1⟩
  abbrev toMulOne (f : Function src dst) := f.toAddZeroMulOne.toMulOne
  end Function
  end AddZeroNegMulOneInv
end



section
  structure ModuleData (K) (E) where
    smul : K → E → E
    scalars : AddZeroNegMulOneInv K
    vectors : OpIdSym E
end

end Algebra