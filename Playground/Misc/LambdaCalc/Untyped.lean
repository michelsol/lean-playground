import Mathlib

inductive Term
| bvar : Nat → Term
| lam : Term → Term
| app : Term → Term → Term

namespace Term
scoped notation:max "#" i => bvar i
scoped notation:max "λ" t => lam t
scoped notation:max t "·" s => app t s

def depths : Term → List (Nat × Nat)
| bvar b => [(b, 0)]
| lam t => t.depths.map λ (b, k) => (b, k + 1)
| app t1 t2 => t1.depths ++ t2.depths

def substBound (t : Term) (j : Nat) (a : Term) : Term := match t with
| bvar i => if i = j then a else bvar i
| lam t => lam (t.substBound (j+1) a)
| app t1 t2 => app (t1.substBound j a) (t2.substBound j a)
-- scoped notation:max t "[" a "]"  => substTop t a

def substTop (t : Term) (a : Term) := match t with
| bvar i => bvar i
| lam t => t.substBound 0 a
| app t1 t2 => app t1 t2

theorem substBound_depths_of
  (p : Nat × Nat → Prop)
  (hp : ∀ {k i j}, p (k, i) → i < j → p (k, j))
  {t : Term} (ht : ∀ x ∈ t.depths, p x)
  (v : Nat)
  {a : Term} (ha : ∀ x ∈ a.depths, p x) :
  ∀ x ∈ (t.substBound v a).depths, p x := by
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

def WellFormed (t : Term) := ∀ x ∈ t.depths, x.1 < x.2
instance (t : Term) : Decidable t.WellFormed := t.depths.decidableBall

theorem WellFormed.substBound
  {t : Term} (ht : t.WellFormed) (j : Nat)
  {a : Term} (ha : a.WellFormed) :
  (t.substBound j a).WellFormed :=
  substBound_depths_of _ Nat.lt_trans ht j ha


def FreeTop (t : Term) := ∀ x ∈ t.depths, x.1 + 1 < x.2

theorem WellFormed.of_lam_FreeTop {t : Term} (ht : (lam t).FreeTop)
  : t.WellFormed := by
  have ht : ∀ _, _ := ht
  erw [List.forall_mem_map_iff] at ht
  intro x hx
  apply Nat.succ_lt_succ_iff.mp
  exact ht x hx

theorem th -- this is false
  (p : Nat × Nat → Prop)
  (hp : ∀ {k i j}, p (k, i) → i < j → p (k, j))
  (v : Nat)
  {t : Term} (ht : ∀ x ∈ t.depths, p (x.1, x.2 + 1))
  {a : Term} (ha : ∀ x ∈ a.depths, p x) :
  ∀ x ∈ (t.substBound v a).depths, p (x.1, x.2 + if v = 0 then 0 else 1) := by
  induction t generalizing p a v with
  | bvar i =>
    have := ht (i, 0) (List.mem_singleton_self _)
    dsimp at this
    show ∀ _ ∈ depths (ite ..), _
    by_cases hi : i = v
    . rw [if_pos hi]
      -- exact ha
      sorry
    . rw [if_neg hi]
      simp [depths]
      sorry
  | app t1 t2 ih1 ih2 =>
    erw [List.forall_mem_append] at ht ⊢
    constructor
    . exact ih1 p hp v ht.1 ha
    . exact ih2 p hp v ht.2 ha
  | lam t ih =>
    erw [List.forall_mem_map_iff] at ht ⊢
    dsimp at ht ⊢
    intro x hx
    by_cases hv : v = 0
    . sorry
    . rw [if_neg hv]
      have ih2 (p : ℕ × ℕ → Prop) hp v ht {a} ha (x : ℕ × ℕ) hx : p (x.1, x.2 + 1) := by
        have := ih p hp (v+1) ht (a := a) ha x hx
        have hv : v + 1 ≠ 0 := sorry
        rw [if_neg hv] at this
        exact this
      apply ih2 λ (x1, x2) => p (x1, x2 + 1)
      . exact hx
      . intro k i j hki hij
        exact hp hki (Nat.succ_lt_succ hij)
      . intro (k, i) hki
        dsimp
        -- exact hp (ha _ hki) (Nat.lt.base i)
        sorry
      .
        dsimp
        sorry
        -- exact hx

theorem WellFormed.substTop_of
  {t : Term} (ht : t.WellFormed)
  {a : Term} (ha : a.WellFormed) :
  (t.substTop a).WellFormed := match t with
  | bvar .. => ht
  | lam t => by
    have ht : ∀ _, _ := ht
    apply th Nat.lt.uncurry Nat.lt_trans 0 ?_ ha
    erw [List.forall_mem_map_iff] at ht
    exact ht
  | app .. => ht


end Term
