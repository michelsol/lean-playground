import Mathlib

variable (α β) in
inductive PTerm
| fvar : α → PTerm
| bvar : β → PTerm
| lam : PTerm → PTerm
| app : PTerm → PTerm → PTerm

namespace PTerm

def mapBound (f : β → β') : PTerm α β → PTerm α β'
  | fvar a => fvar a
  | bvar b => bvar (f b)
  | lam t => lam (t.mapBound f)
  | app t1 t2 => app (t1.mapBound f) (t2.mapBound f)

def toBoundDepthTree : PTerm α β → PTerm α (β × Nat)
| fvar a => fvar a
| bvar b => bvar (b, 0)
| lam t => lam (t.toBoundDepthTree.mapBound λ (b, k) => (b, k + 1))
| app t1 t2 => app t1.toBoundDepthTree t2.toBoundDepthTree

def subst [DecidableEq α] (t : PTerm α β) (v : α) (a : PTerm α β) : PTerm α β := match t with
| bvar i => bvar i
| fvar x => if x = v then a else fvar x
| lam t => lam (t.subst v a)
| app t1 t2 => app (t1.subst v a) (t2.subst v a)
scoped notation:max t "[" v " := " a "]"  => subst t v a


variable {α β} (p : β → Prop) in
inductive AllBound : PTerm α β → Prop
| fvar (a) : AllBound (fvar a)
| bvar : p b → AllBound (bvar b)
| lam : AllBound t → AllBound (lam t)
| app : AllBound t1 → AllBound t2 → AllBound (app t1 t2)

theorem AllBound.mapBound_iff (t : PTerm α β) (f : β → β') :
  (t.mapBound f).AllBound p ↔ t.AllBound (p ∘ f) := by
  induction t with
  | fvar a =>
    constructor
    . intro _; exact .fvar _
    . intro _; exact .fvar _
  | bvar b =>
    constructor
    . intro (.bvar h); exact .bvar h
    . intro (.bvar h); exact .bvar h
  | lam t ih =>
    constructor
    . intro (.lam h); exact .lam $ ih.mp h
    . intro (.lam h); exact .lam $ ih.mpr h
  | app t1 t2 ih1 ih2 =>
    constructor
    . intro (.app h1 h2)
      constructor
      . exact ih1.mp h1
      . exact ih2.mp h2
    . intro (.app h1 h2)
      constructor
      . exact ih1.mpr h1
      . exact ih2.mpr h2

theorem AllBound.of_sub {p q} (hpq : ∀ x, p x → q x) {t : PTerm α β}
  (hp : t.AllBound p) : t.AllBound q := by
  induction hp with
  | fvar a => exact .fvar a
  | bvar hb => exact .bvar $ hpq _ hb
  | lam _ ih => exact .lam ih
  | app _ _ ih1 ih2 => exact .app ih1 ih2

theorem AllBound.subst_toBoundDepthTree_of
  [DecidableEq α]
  (p : β → ℕ → Prop)
  (hp : ∀ {k i j}, p k i → i < j → p k j)
  {t} (ht : t.toBoundDepthTree.AllBound p.uncurry)
  (v : α)
  {a} (ha : a.toBoundDepthTree.AllBound p.uncurry) :
  t[v := a].toBoundDepthTree.AllBound p.uncurry := by
  induction t generalizing p a with
  | bvar i => exact ht
  | fvar x =>
    show AllBound _ (toBoundDepthTree (ite ..))
    by_cases hx : x = v
    . rw [if_pos hx]; exact ha
    . rw [if_neg hx]; exact ht
  | app t1 t2 ih1 ih2 =>
    let .app h1 h2 := ht
    apply app
    . exact ih1 p hp h1 ha
    . exact ih2 p hp h2 ha
  | lam t ih =>
    let .lam hs := ht
    apply lam
    rw [AllBound.mapBound_iff] at hs ⊢
    apply ih (λ x1 x2 => p x1 (x2 + 1)) ?_ hs
    . apply ha.of_sub
      intro (k, i) hki
      exact hp hki (Nat.lt.base i)
    . intro k i j hki hij
      exact hp hki (Nat.succ_lt_succ hij)


end PTerm

def Term := PTerm Nat Nat

namespace Term
open PTerm
@[match_pattern] def bvar : Nat → Term := .bvar
@[match_pattern] def fvar : Nat → Term := .fvar
@[match_pattern] def lam : Term → Term := .lam
@[match_pattern] def app : Term → Term → Term := .app

scoped notation:max "♭" i => bvar i
scoped notation:max "♯" x => fvar x
scoped notation:max "λ" t => lam t
scoped notation:max t "·" s => app t s

def WellFormed (t : Term) := t.toBoundDepthTree.AllBound (.<.).uncurry

theorem WellFormed.subst_of
  (t : Term) (ht : t.WellFormed)
  (v : Nat)
  (a : Term) (ha : a.WellFormed) :
  WellFormed t[v := a] :=
  ht.subst_toBoundDepthTree_of Nat.lt Nat.lt_trans v ha

#exit

def substBound (t : Term) (j : Nat) (a : Term) : Term := match t with
| bvar i => if i = j then a else bvar i
| fvar x => fvar x
| lam t => lam (t.substBound (j+1) a)
| app t1 t2 => app (t1.substBound j a) (t2.substBound j a)

def substTop (t : Term) (a : Term) : Term := substBound t 0 a

end Term
