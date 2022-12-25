import Mathlib

namespace STLC

inductive τ : Type
| base : τ
| arrow : τ → τ → τ
deriving Repr

inductive Term : Type
| base : Term
| var : ℕ → Term
| abs : ℕ → τ → Term → Term
| app : Term → Term → Term
deriving Repr

-- this is wrong because one is allowed to build badly typed apps

namespace Term

scoped infixl:1000 "→" => τ.arrow
scoped notation:1001 "τ₀" => τ.base

scoped notation:1001 "c₀" => Term.base
scoped prefix:max "#" => var
scoped notation:max "λ" x ":" a "⬝" t => abs x a t
scoped notation:max a " @ " b => app a b

#reduce λ0:τ₀⬝#0

abbrev TermWithType := Term × τ

inductive Typing : List TermWithType → TermWithType → Prop
| base : Typing [] (c₀, τ₀)
| var {Γ x t} : ((#x, t) ∈ Γ) → Typing Γ (#x, t)
| abs {Γ x e s t} : Typing ((#x, s) :: Γ) (e, t) → Typing Γ (λ x : s ⬝ e, s → t)
| app {Γ f s t e} : Typing Γ (f, s → t) → Typing Γ (e, s) → Typing Γ (f @ e, t)

scoped notation:max a " ⊢ " b => Typing a b

example : [] ⊢ (λ0:τ₀⬝#0, τ₀ → τ₀) := by
  apply Typing.abs
  apply Typing.var
  exact List.mem_singleton.mpr rfl

-- TODO : mix Typing and Term, in a single inductive to only allow constructing valid Terms

end Term
end STLC
