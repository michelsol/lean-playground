import Playground.Formal.Logic.System
import Playground.Formal.Logic.OrderZero.Connectives
import Playground.Formal.Logic.Truth

namespace Formal.Logic
abbrev Theory (L) [Language L] := Set (Formula L)

namespace Theory
open OrderZero.Connectives

section
  variable {L} [Language L] [System L] [Not L]

  open System Formal.System in
  def SystemProves (S : Theory L) (f : Formula L) := (map <$> S) ⊢[L] (map f)
  scoped notation:max S " ⊢ " f => SystemProves S f
  scoped notation:max S " ⊬ " f => Not (SystemProves S f)

  def IsSyntacticallyConsistent (T : Theory L) := ∀ f, Not ((T ⊢ f) ∧ (T ⊢ ¬f))
  def IsSyntacticallyComplete (T : Theory L) := ∀ f, (T ⊢ f) ∨ (T ⊢ ¬f) -- T=PA is not complete
  def theorems (T : Theory L) := { f | T ⊢ f }
end

section
  variable {L} [Language L] [Truth.Assignment L] [Not L]

  open Truth
  def EntailsUnder (i : Truth.Interpretation L) (T : Theory L) (f : Formula L) :=
    (∀ g ∈ T, ⊨[i] g) → ⊨[i] f
  scoped notation:40 T " ⊨[" i "] " f  => EntailsUnder i T f
  def Entails (T : Theory L) (f : Formula L) := ∀ i, T ⊨[i] f
  scoped notation:40 T " ⊨ " f  => Entails T f

  def IsSemanticallyConsistent (T : Theory L) := ∀ f, Not ((T ⊨ f) ∧ (T ⊨ ¬f))
  def IsSemanticallyComplete (T : Theory L) := ∀ f, (T ⊨ f) ∨ (T ⊨ ¬f)
  def consequences (T : Theory L) := { f | T ⊨ f }
end

section
  variable {L} [Language L] [System L] [Truth.Assignment L]

  def IsSound (T : Theory L) := ∀ f, (T ⊢ f) → (T ⊨ f)
  def IsComplete (T : Theory L) := ∀ f, (T ⊨ f) → (T ⊢ f) -- any FOL theory is complete (even T=PA)
end

end Theory
end Formal.Logic
