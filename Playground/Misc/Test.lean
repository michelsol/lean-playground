
class Ref (σ : Type) (m : Type → Type) where
  Data (α) : Type
  mkRef {α} (a : α) : m (Data α)

namespace Ref
class Get (σ) (m) [Ref σ m] where
  get {α} (r : Data σ m α) : m α
def Data.get {σ} {m} [Ref σ m] [Get σ m] {α} : Data σ m α → m α := Get.get

class Set (σ) (m) [Ref σ m] where
  set {α} (r : Data σ m α) (v : α) : m Unit
def Data.set {σ} {m} [Ref σ m] [Set σ m] {α} : Data σ m α → α → m Unit := Set.set

instance {σ} : Ref σ (ST σ) where
  Data := ST.Ref σ
  mkRef := ST.mkRef
instance {σ} : Get σ (ST σ) where get := ST.Ref.get
instance {σ} : Set σ (ST σ) where set x a := ST.Ref.set x a

instance : Ref IO.RealWorld IO where
  Data := IO.Ref
  mkRef x := IO.mkRef x
instance : Get IO.RealWorld IO where get := ST.Ref.get
instance : Set IO.RealWorld IO where set := ST.Ref.set
end Ref

def code0 (σ) {m} [Monad m] [Ref σ m] [Ref.Get σ m] [Ref.Set σ m] : m Nat := do
  let x : Ref.Data σ m Nat ← Ref.mkRef 1
  x.set 2
  let r ← x.get
  return r

def code3 {m} [Monad m] 
  (σ) [Ref σ m] [Ref.Get σ m] [Ref.Set σ m]
  {cst} [Ref cst m] [Ref.Get cst m]
  (i : Ref.Data cst m Nat)
 : m Nat := do
  let x : Ref.Data σ m Nat ← Ref.mkRef 1
  x.set (← i.get)
  let r ← x.get
  return r

open ST in
def code1 (σ) {m} [Monad m] [MonadLiftT (ST σ) m] : m Nat := do
  let x : Ref σ Nat ← mkRef 1
  x.set 2
  let r ← x.get
  return r

def code2 (σ : Type) : ST σ Nat := do
  let x : ST.Ref σ Nat ← ST.mkRef 1
  x.set 2
  let r ← x.get
  return r

def c : IO Unit := do
  let r ← code0 (IO.RealWorld)
  IO.println s!"r = {r}"
  return ()

#eval c