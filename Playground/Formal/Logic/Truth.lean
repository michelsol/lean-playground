import Playground.Formal.Logic.Language

namespace Formal.Logic
namespace Truth

class Assignment (L) [Language L] where
  Interpretation : Type _
  IsTrueUnder : Interpretation → Formula L → Prop

export Assignment (Interpretation IsTrueUnder)
scoped notation:max "⊨[" i "] " f  => IsTrueUnder i f

def IsTrue {L} [Language L] [Assignment L] (f : Formula L) := ∀ i, ⊨[i] f
scoped notation:max "⊨ " f  => IsTrue f

end Truth
end Formal.Logic
