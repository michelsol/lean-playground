import Mathlib.Init.Set

namespace Formal

section
  class Judgments (L : Type _) where
    Judgment : Type _
  export Judgments (Judgment)
  class System (L) extends Judgments L where
    Proves : Set Judgment → Judgment → Prop

  namespace System
  scoped notation:max t " ⊢ " j => System.Proves t j
  scoped notation:max t " ⊬ " j => ¬(System.Proves t j)
  abbrev SystemProves L [System L] := System.Proves (L := L)
  scoped notation:max t " ⊢[" L "] " j => SystemProves L t j
  scoped notation:max t " ⊬[" L "] " j => ¬(SystemProves L t j)
  end System
end

section
  structure Rule (L) [Judgments L] where
    {arity : Nat}
    premisses : Fin arity → Judgment L
    conclusion : Judgment L

  namespace RuleBased
  variable (L) [Judgments L]
  variable (R : Set (Rule L))
  variable (T : Set (Judgment L))
  inductive Proof : Judgment L → Prop
  | hypo (_ : j ∈ T) : Proof j
  | rule (_ : r ∈ R) (_ : ∀ k, Proof $ r.premisses k) : Proof r.conclusion

  class System (L) [Judgments L] (R : Set (Rule L))
  -- todo change to instance
  example {L} [Judgments L] {R} [System L R] : Formal.System L where
    Proves := Proof L R
  end RuleBased
end

end Formal
