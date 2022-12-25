import Mathlib

inductive Term
| fvar : Nat → Term
| bvar : Nat → Term
| lam : Term → Term
| app : Term → Term → Term

namespace Term
scoped notation:max "♭" i => bvar i
scoped notation:max "♯" x => fvar x
scoped notation:max "λ" t => lam t
scoped notation:max t "·" s => app t s

def bvarsDepths : Term → List (Nat × Nat)
| fvar _ => []
| bvar b => [(b, 0)]
| lam t => t.bvarsDepths.map λ (b, k) => (b, k + 1)
| app t1 t2 => t1.bvarsDepths ++ t2.bvarsDepths

def fvars : Term → List Nat
| bvar _ => []
| fvar x => [x]
| lam t => t.fvars
| app t1 t2 => t1.fvars ++ t2.fvars

def subst (t : Term) (v : Nat) (a : Term) : Term := match t with
| bvar i => bvar i
| fvar x => if x = v then a else fvar x
| lam t => lam (t.subst v a)
| app t1 t2 => app (t1.subst v a) (t2.subst v a)
scoped notation:max t "[" v " := " a "]"  => subst t v a

theorem subst_bvarsDepths_of
  (p : Nat × Nat → Prop)
  (hp : ∀ {k i j}, p (k, i) → i < j → p (k, j))
  {t : Term} (ht : ∀ x ∈ t.bvarsDepths, p x)
  (v : Nat)
  {a : Term} (ha : ∀ x ∈ a.bvarsDepths, p x) :
  ∀ x ∈ t[v := a].bvarsDepths, p x := by
  induction t generalizing p a with
  | bvar i => exact ht
  | fvar x =>
    show ∀ _ ∈ bvarsDepths (ite ..), _
    by_cases hx : x = v
    . rw [if_pos hx]; exact ha
    . rw [if_neg hx]; exact ht
  | app t1 t2 ih1 ih2 =>
    erw [List.forall_mem_append] at ht ⊢
    constructor
    . exact ih1 p hp ht.1 ha
    . exact ih2 p hp ht.2 ha
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


def WellFormed (t : Term) := ∀ x ∈ t.bvarsDepths, x.1 < x.2
instance (t : Term) : Decidable t.WellFormed := t.bvarsDepths.decidableBall

def Closed (t : Term) := t.fvars = []
instance (t : Term) : Decidable t.Closed := show Decidable (_ = []) from inferInstance

theorem WellFormed.subst_of {t} (ht : t.WellFormed) (v : Nat) {a} (ha : a.WellFormed) :
  t[v := a].WellFormed :=
  subst_bvarsDepths_of _ Nat.lt_trans ht v ha

def decidableEq : DecidableEq Term
| .bvar _, .bvar _ => by rw [bvar.injEq]; infer_instance
| .bvar .., .fvar .. => isFalse Term.noConfusion
| .bvar .., .lam .. => isFalse Term.noConfusion
| .bvar .., .app .. => isFalse Term.noConfusion
| .fvar .., .bvar .. => isFalse Term.noConfusion
| .fvar _, .fvar _ => by rw [fvar.injEq]; infer_instance
| .fvar .., .lam .. => isFalse Term.noConfusion
| .fvar .., .app .. => isFalse Term.noConfusion
| .lam .., .bvar .. => isFalse Term.noConfusion
| .lam .., .fvar .. => isFalse Term.noConfusion
| .lam t, .lam t' => by rw [lam.injEq]; let _ := decidableEq t t'; infer_instance
| .lam .., .app .. => isFalse Term.noConfusion
| .app .., .bvar .. => isFalse Term.noConfusion
| .app .., .fvar .. => isFalse Term.noConfusion
| .app .., .lam .. => isFalse Term.noConfusion
| .app t₁ t₂, .app t₁' t₂' => by
  rw [app.injEq]
  let _ := decidableEq t₁ t₁'
  let _ := decidableEq t₂ t₂'
  infer_instance
instance : DecidableEq Term := decidableEq

end Term

-- unicity of cardinal comes from this deep lemma : Perm.perm_ext  even deeper lemma : Sublist.eq_of_length
