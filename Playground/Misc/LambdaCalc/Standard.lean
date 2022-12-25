import Mathlib

inductive Lambda where
| var (x : Nat)
| lam (x : Nat) (t : Lambda)
| app (f t : Lambda)

namespace Lambda
scoped notation:max "#" x => var x
scoped notation:max "λ" x "⬝" t => lam x t
scoped notation:max f "·" t => app f t

def repr : Lambda → String
| #x => x.repr
| λx⬝t => "(λ" ++ x.repr ++ "⬝" ++ t.repr ++ ")"
| f·t => "(" ++ f.repr ++ "·" ++ t.repr ++ ")"

instance : Repr Lambda := ⟨λ t _ => t.repr⟩
instance : ToString Lambda := ⟨repr⟩
instance (n) : OfNat Lambda n := ⟨#n⟩

inductive Mem (x : Nat) : Lambda → Prop
| var : (#x).Mem x
| lam_t {t} {y} : t.Mem x → (λy⬝t).Mem x
| lam_x {t} : (λx⬝t).Mem x
| app_f {f t} : f.Mem x → (f·t).Mem x
| app_t {f t} : t.Mem x → (f·t).Mem x
instance : Membership Nat Lambda := ⟨Mem⟩

theorem Mem_var_iff (v) (x) : v ∈ (#x) ↔ v = x := by
  constructor
  . intro h; cases h with | var => rfl
  . intro h; rw [h]; exact .var

theorem Mem_lam_iff (v) (x) (f) : v ∈ (λx⬝f) ↔ (v = x ∨ v ∈ f) := by
  constructor
  . intro h; cases h with
    | lam_t h => exact .inr h
    | lam_x => exact .inl rfl
  . intro h; cases h with
    | inl h => rw [h]; exact .lam_x
    | inr h => exact .lam_t h

theorem Mem_app_iff (v) (f t) : v ∈ (f·t) ↔ (v ∈ f ∨ v ∈ t) := by
  constructor
  . intro h; cases h with
    | app_f hf => exact .inl hf
    | app_t ht => exact .inr ht
  . intro h; cases h with
    | inl h => exact .app_f h
    | inr h => exact .app_t h

def decidableMem (x : Nat) (t : Lambda) : Decidable (x ∈ t) := by
  match t with
  | var y => rw [Mem_var_iff]; infer_instance
  | lam y u => rw [Mem_lam_iff]; let _ := u.decidableMem x; infer_instance
  | app g u =>
    rw [Mem_app_iff]
    let _ := g.decidableMem x
    let _ := u.decidableMem x
    infer_instance
instance (x : Nat) : (t : Lambda) → Decidable (x ∈ t) := decidableMem x

def decidableEq : DecidableEq Lambda
| .var x, .var x' => by rw [var.injEq]; infer_instance
| .var .., .lam .. => isFalse Lambda.noConfusion
| .var .., .app .. => isFalse Lambda.noConfusion
| .lam .., .var .. => isFalse Lambda.noConfusion
| .lam x t, .lam x' t' => by rw [lam.injEq]; let _ := decidableEq t t'; infer_instance
| .lam .., .app .. => isFalse Lambda.noConfusion
| .app .., .var .. => isFalse Lambda.noConfusion
| .app .., .lam .. => isFalse Lambda.noConfusion
| .app f t, .app f' t' => by
  rw [app.injEq]
  let _ := decidableEq f f'
  let _ := decidableEq t t'
  infer_instance
instance : DecidableEq Lambda := decidableEq


inductive ValidSubst : Lambda → Nat → Lambda → Type
| var {x y} {t} : (#y).ValidSubst x t
| lam {x y} {t u} : y ≠ x → y ∉ t → u.ValidSubst x t → (λy⬝u).ValidSubst x t
| app {x} {g u t} : g.ValidSubst x t → u.ValidSubst x t → (g·u).ValidSubst x t
scoped notation:max f "[" x " := " t "] valid" => ValidSubst f x t

def decValidSubst (f : Lambda) (x : Nat) (t : Lambda) : Option (f[x := t] valid) :=
  match f, x, t with
  | #_, _, _ => some .var
  | λy⬝u, x, t =>
    if hx : y = x then none else
      if ht : y ∈ t then none else
        (u.decValidSubst x t).map (.lam hx ht)
  | g·u, x, t =>
    -- Option.map₂ ValidSubst.app (g.decValidSubst x t) (u.decValidSubst x t)
    match g.decValidSubst x t, u.decValidSubst x t with
    | some hg, some hu => some $ .app hg hu
    | none, some _ => none
    | some _, none => none
    | none, none => none


def uncheckedSubst (f : Lambda) (x : Nat) (t : Lambda) : Lambda :=
  match f, x, t with
  | #y, x, t => if y = x then t else #y
  | λy⬝u, x, t => λy⬝u.uncheckedSubst x t
  | g·u, x, t => (g.uncheckedSubst x t)·(u.uncheckedSubst x t)

def checkedSubst (f : Lambda) (x : Nat) (t : Lambda) (_ : f[x := t] valid) : Lambda :=
  uncheckedSubst f x t
scoped notation:max f "[" x " := " t ", " h "]"  => checkedSubst f x t h

def decSubst (f : Lambda) (x : Nat) (t : Lambda) : Lambda :=
  match f.decValidSubst x t with
  | none => f
  | some _ => f.uncheckedSubst x t
-- scoped notation:max f "[" x " := " t "]"  => subst f x t



def freshVar : Lambda → Nat
| #x => x + 1
| λx⬝t => max x t.freshVar + 1
| f·t => max f.freshVar t.freshVar + 1

theorem lt_freshVar_of_Mem {t : Lambda} {v} : v ∈ t → v < t.freshVar := by
  intro hv; induction hv with
  | var => apply Nat.le_refl
  | lam_t _ ih =>
    apply Nat.lt_trans ih
    apply Nat.succ_le_succ
    apply Nat.le_max_right
  | lam_x =>
    apply Nat.succ_le_succ
    apply Nat.le_max_left
  | app_f _ ih =>
    apply Nat.lt_trans ih
    apply Nat.succ_le_succ
    apply Nat.le_max_left
  | app_t _ ih =>
    apply Nat.lt_trans ih
    apply Nat.succ_le_succ
    apply Nat.le_max_right

theorem freshVar_not_Mem (t : Lambda) : t.freshVar ∉ t :=
  λ c => Nat.lt_irrefl _ (t.lt_freshVar_of_Mem c)

def size : Lambda → Nat
| #_ => 1
| λ_⬝t => t.size + 1
| f·t => f.size + t.size + 1

def renameVar : Lambda → Nat → Nat → Lambda
  | #y, x, z => if y = x then #z else #y
  | λy⬝u, x, z => λy⬝u.renameVar x z
  | g·u, x, z => (g.renameVar x z)·(u.renameVar x z)

theorem renameVar_size (f : Lambda) (x z : Nat) : (f.renameVar x z).size = f.size := by
  induction f with
  | var y =>
    show size (ite ..) = _
    by_cases h : y = x
    . rw [if_pos h]; rfl
    . rw [if_neg h]
  | lam _ u ihu =>
    show _ + _ = _ + _
    rw [ihu]
  | app g u ihg ihu =>
    show _ + _ + _ = _ + _ + _
    rw [ihg, ihu]

def safen : Lambda → Nat → Lambda → Lambda
  | #y, _, _ => #y
  | λy⬝u, x, t =>
      if y = x ∨ y ∈ t then
        let z := max x t.freshVar + 1
        have : (u.renameVar y z).size < size λy⬝u := by simp_arith [size, renameVar_size]
        λz⬝(u.renameVar y z).safen x t
      else
        have : u.size < size λy⬝u := by simp_arith [size]
        λy⬝u.safen x t
  | g·u, x, t =>
    have : g.size < size (g·u) := by simp_arith [size]
    have : u.size < size (g·u) := by simp_arith [size]
    (g.safen x t)·(u.safen x t)
termination_by _ f _ _ => f.size

def safen_valid : (f : Lambda) → (x : Nat) → (t : Lambda) → (f.safen x t)[x := t] valid
  | #y, x, t => .var
  | λy⬝u, x, t => by
    let z := max x t.freshVar + 1
    show (
      if y = x ∨ y ∈ t then
        λz⬝(u.renameVar y z).safen x t
      else
        λy⬝u.safen x t
      )[x := t] valid
    by_cases hyx : y = x ∨ y ∈ t
    . rw [if_pos hyx]
      apply ValidSubst.lam
      . apply Nat.ne_of_gt
        apply Iff.mpr Nat.lt_succ
        exact Nat.le_max_left x t.freshVar
      . intro hc
        apply Nat.not_le_of_lt (lt_freshVar_of_Mem hc)
        apply Nat.le_trans _ (Nat.le_add_right _ 1)
        . exact Nat.le_max_right x t.freshVar
      . have : (u.renameVar y z).size < size λy⬝u := by simp_arith [size, renameVar_size]
        exact (u.renameVar y z).safen_valid x t
    . rw [if_neg hyx]
      apply ValidSubst.lam
      . intro c; apply hyx; exact .inl c
      . intro c; apply hyx; exact .inr c
      . have : u.size < size λy⬝u := by simp_arith [size]
        exact u.safen_valid x t
  | g·u, x, t => by
    show ((g.safen x t)·(u.safen x t))[x := t] valid
    apply ValidSubst.app
    . have : g.size < size (g·u) := by simp_arith [size]
      exact g.safen_valid x t
    . have : u.size < size (g·u) := by simp_arith [size]
      exact u.safen_valid x t
termination_by _ f _ _ => f.size

def safeSubst (f : Lambda) (x : Nat) (t : Lambda) : Lambda :=
  (f.safen x t).checkedSubst x t (f.safen_valid x t)
scoped notation:max f "[" x " := " t "]"  => safeSubst f x t


-- #eval (λ0⬝(1·0))[1 := λ1⬝1]

inductive AlphaEq : Lambda → Lambda → Prop
| r1 : (h : m[x := #y] valid) → AlphaEq (λx⬝m) (λy⬝m[x := #y, h])
| r2 : AlphaEq m n → AlphaEq (λx⬝m) (λx⬝n)
| r3 : AlphaEq m m' → AlphaEq n n' → AlphaEq (m.app n) (m'.app n')

inductive Reduction : Lambda → Lambda → Prop
| r1 : Reduction m m' → Reduction (m·n) (m'·n)
| r2 : Reduction n n' → Reduction (m·n) (m·n')
| r3 : Reduction m n → Reduction (λx⬝m) (λx⬝n)
| r4 : (h : m[x := n] valid) → Reduction ((λx⬝m)·n) m[x := n, h]

partial def reduce : Lambda → Lambda
| #x => #x
| λx⬝m => λx⬝m.reduce
| (#x)·n => (#x).reduce·n.reduce
| (λx⬝m)·n => (m[x := n]).reduce
| (l·m)·n => (l·m).reduce·n.reduce

-- #eval ((λ1⬝1·1)·3).reduce


end Lambda
