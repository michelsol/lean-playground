-- import Mathlib

namespace Lambda

inductive Term (v : Type) : Type
| var : v → Term v
| lam : (v → Term v) → Term v
| app : Term v → Term v → Term v

namespace Term

def squash : Term (Term v) → Term v
| var x => x
| lam f => lam fun x => (f (var x)).squash
| app e t => app e.squash t.squash

def Closed := {v : _} → Term v
def Free := {v : _} → v → Term v
def Free.subst (e : Free) (t : Closed) : Closed := (e t).squash
def subst (e : Free) (t : Term v) : Term v := (e t).squash

def lift_f (f : v → Term v) : Term v → Term (Term v)
  | var x => var (f x)
  | lam g =>
  -- let g' := lift_f g
  var (lam g)
  | app e t => var (app e t)


#exit
def reduce : Term v → Term v
  | var x => var x
  | lam f => lam λ x => (f x).reduce
  | app (var x) t => app (var x).reduce t.reduce
  -- | app (lam f) t => (lift_f f t).squash.reduce
  | app (lam f) (var x) => (f x).reduce
  | app (lam f) (lam g) => app (lam f).reduce (lam g).reduce
  | app (lam f) (app e t) => app (lam f).reduce (app e t).reduce
  | app (app e s) t => app (app e s).reduce t.reduce

namespace Closed
def reduce (t : Closed) : Closed := λ {v} => (@t v).reduce

def lamxx : Closed := lam var
def lamxxAty : Free := fun y => app (lam var) (var y)
-- #reduce lamxxAty
-- #reduce lamxxAty.subst lamxx
def lamxxAty2 (y : v) := app (lam var) (var y)
-- #reduce λ y => (lamxxAty2 y).reduce


end Closed
end Term
end Lambda
