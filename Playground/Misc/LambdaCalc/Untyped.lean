import Mathlib

inductive Term
| bvar : Nat → Term
| lam : Term → Term
| app : Term → Term → Term
deriving Repr

namespace Term
scoped notation:max "#" i => bvar i
scoped notation:max "λ" t => lam t
scoped notation:max t "·" s => app t s

def decidableEq : DecidableEq Term
| .bvar x, .bvar x' => by rw [bvar.injEq]; infer_instance
| .bvar .., .lam .. => isFalse Term.noConfusion
| .bvar .., .app .. => isFalse Term.noConfusion
| .lam .., .bvar .. => isFalse Term.noConfusion
| .lam t, .lam t' => by rw [lam.injEq]; let _ := decidableEq t t'; infer_instance
| .lam .., .app .. => isFalse Term.noConfusion
| .app .., .bvar .. => isFalse Term.noConfusion
| .app .., .lam .. => isFalse Term.noConfusion
| .app a b, .app a' b' => by
  rw [app.injEq]
  let _ := decidableEq a a'
  let _ := decidableEq b b'
  infer_instance
instance : DecidableEq Term := decidableEq

def depths : Term → List (Nat × Nat)
| bvar b => [(b, 0)]
| lam t => t.depths.map λ (b, k) => (b, k + 1)
| app t1 t2 => t1.depths ++ t2.depths

def WellFormed (t : Term) := ∀ x ∈ t.depths, x.1 < x.2
instance (t : Term) : Decidable t.WellFormed := t.depths.decidableBall


def subst (t : Term) (j : Nat) (a : Term) : Term := match t with
| bvar i => if i = j then a else bvar i
| lam t => lam (t.subst (j+1) a)
| app t1 t2 => app (t1.subst j a) (t2.subst j a)
scoped notation:max t "[" j " := " a "]"  => subst t j a

theorem subst_depths_of
  (p : Nat × Nat → Prop)
  (hp : ∀ {k i j}, p (k, i) → i < j → p (k, j))
  {t : Term} (ht : ∀ x ∈ t.depths, p x)
  (v : Nat)
  {a : Term} (ha : ∀ x ∈ a.depths, p x) :
  ∀ x ∈ t[v := a].depths, p x := by
  induction t generalizing p a v with
  | bvar i =>
    show ∀ _ ∈ depths (ite ..), _
    by_cases hi : i = v
    . rw [if_pos hi]; exact ha
    . rw [if_neg hi]; exact ht
  | app t1 t2 ih1 ih2 =>
    erw [List.forall_mem_append] at ht ⊢
    constructor
    . exact ih1 p hp ht.1 v ha
    . exact ih2 p hp ht.2 v ha
  | lam t ih =>
    erw [List.forall_mem_map_iff] at ht ⊢
    dsimp at ht ⊢
    intro x hx
    apply ih λ (x1, x2) => p (x1, x2 + 1)
    . intro k i j hki hij
      exact hp hki (Nat.succ_lt_succ hij)
    . exact ht
    . intro (k, i) hki
      exact hp (ha _ hki) (Nat.lt.base i)
    . exact hx

theorem WellFormed.subst {t} (ht : t.WellFormed) (j) {a} (ha : a.WellFormed) :
  t[j := a].WellFormed :=
  subst_depths_of Nat.lt.uncurry Nat.lt_trans ht j ha

theorem WellFormed.subst_zero
  {t : Term} (ht : (λt).WellFormed)
  {a : Term} (ha : a.WellFormed) :
  t[0 := a].WellFormed := by
    sorry

-- #reduce (λ#0)·#1

inductive BetaRed : Term → Term → Prop
| r1 : BetaRed m m' → BetaRed (m·n) (m'·n)
| r2 : BetaRed n n' → BetaRed (m·n) (m·n')
| r3 : BetaRed m n → BetaRed (λm) (λn)
| r4 : BetaRed ((λm)·n) m[0 := n]

def BetaEqv := EqvGen BetaRed
scoped infixl:60 " ~ " => BetaEqv
-- two β ~ lambda terms represent the same program

def isNormal (t : Term) := ∀ ⦃s⦄, ¬BetaRed t s

-- we use polish notation for applications to avoid handling parentheses
inductive Alphabet
| lam
| app
| bvar (b : Nat)

def toStr : Term → List Alphabet
| bvar b => [.bvar b]
| lam t => .lam :: t.toStr
| app t1 t2 => .app :: t1.toStr ++ t2.toStr

partial def parse : List Alphabet → (Option Term) × List Alphabet
| [] => (none, [])
| .bvar b :: l => (some $ bvar b, l)
| .lam :: l =>
  let (t, l1) := parse l
  (t.map lam, l1)
| .app :: l =>
  let (ot1, l1) := parse l
  let (ot2, l2) := parse l1
  (do
    let t1 ← ot1
    let t2 ← ot2
    some $ app t1 t2, l2)

def ofStr (l : List Alphabet) := (parse l).1

-- #eval ((λ#0)·#1)
-- #eval ofStr ((λ#0)·#1).toStr


#exit

def true := λλ#1

def false := λλ#0

def ite := λλλ((#2)·#1)·#0



def nat : Nat → Term
| 0 => λ#0
| n + 1 => λ ((#0)·false)·nat n

theorem nat_inj (h : nat n = nat n') : n = n' := by
  match n, n' with
  | 0, 0 => rfl
  | n + 1, n' + 1 =>
    rw [nat_inj (?_ : nat n = nat n')]
    erw [lam.injEq, app.injEq] at h
    exact h.2

def succ := λλ((#0)·false)·#1

theorem nat_succ : nat n.succ ~ succ·nat n := by
  apply EqvGen.symm
  apply EqvGen.trans _ _ _ ?_ (EqvGen.refl _)
  apply EqvGen.rel
  apply BetaRed.r4



end Term
