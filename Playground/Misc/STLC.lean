import Mathlib

namespace STLC

inductive τ : Type _
| base : τ
| arrow : τ → τ → τ
deriving Repr
scoped notation:max "τ₀" => τ.base
scoped notation:max a "⟶" b => τ.arrow a b

abbrev τ.denote : τ → Type _
| base => Unit
| arrow a b => a.denote → b.denote

inductive Term (v : τ → Type) : τ → Type _
| const : Term v τ₀
| var : v t → Term v t
| lam : (v a → Term v b) → Term v (a ⟶ b)
| app : Term v (a ⟶ b) → Term v a → Term v b

namespace Term

def denote : Term τ.denote t → t.denote
| const => ()
| var x => x
| lam f => λ x => denote (f x)
| app f a => denote f (denote a)

def squash : Term (Term v) t → Term v t
| const => const
| var x => x
| lam f => lam λ x => (f (var x)).squash
| app f a => app f.squash a.squash


def Closed (t : τ) := {v : _} → Term v t -- Term with all vars bound
def Free (a b : τ) := {v : _} → v a → Term v b -- b-Term parametrized by one free a-var
def subst (e : Free a b) (t : Closed a) : Closed b := (e t).squash
def subst2 (e : Free a b) (t : Term v a) : Term v b := (e t).squash
def subst3 (e : Term v a → Term (Term v) b) (t : Term v a) : Term v b := (e t).squash

def reduce : Term v t → Term v t
| const => const
| var x => var x
| lam f => lam λ x => (f x).reduce
| app (var x) m => app (var x).reduce m.reduce
| app (app e m) n => app (app e m).reduce n.reduce
| app (lam f) u =>
  -- subst2 (λ {z} => sorry) u
  subst3 sorry u

end Term
end STLC
