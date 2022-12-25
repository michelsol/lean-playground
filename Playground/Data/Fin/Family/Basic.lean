import Mathlib.Logic.Basic
import Playground.Data.Fin.Misc

namespace Fin
@[reducible] def Family (α : Type u) (n : Nat) := Fin n → α

namespace Family
def of {α} {n : Nat} (f : Fin n → α) : Family α n := f

section
  variable {α : Type _}

  def cons {n : Nat} (f : Family α n) (a : α) : Family α (n + 1) :=
    of λ k => match k with
      | ⟨0, hk⟩ => a
      | ⟨k + 1, hk⟩ => f ⟨k, Nat.lt_of_succ_lt_succ hk⟩

  def snoc {n : Nat} (f : Family α n) (a : α) : Family α (n + 1) :=
    of λ k => if c : k.val < n then f ⟨k.val, c⟩ else a

  def head {n : Nat} (f : Family α (n + 1)) : α := f ⟨0, n.zero_lt_succ⟩

  def last {n : Nat} (f : Family α (n + 1)) : α := f ⟨n, n.lt_succ_self⟩

  def tail {n : Nat} (f : Family α (n + 1)) : Family α n :=
    of λ k => f k.succ

  def to_list : {n : Nat} → (f : Family α n) → List α
    | 0, _ => []
    | n + 1, f => f.tail.to_list.cons f.head

  def of_list : (l : List α) → Family α l.length
    | [] => of f0
    | a :: l => (of_list l).cons a
end

section
  @[reducible] def for_all {n : Nat} (p : Family Prop n) : Prop := ∀ k, p k

  def all : {n : Nat} → Family Prop n → Prop
    | 0, _ => True
    | n + 1, p => p.head ∧ p.tail.all

  theorem all_iff_forall {n : Nat} (p : Family Prop n) : p.all ↔ ∀ k, p k :=
    ⟨let rec forall_of_all {n : Nat} (p : Family Prop n) : p.all → ∀ k, p k :=
      λ h => match n with
        | 0 => f0
        | n + 1 => λ k => match k with
          | ⟨0, hk⟩ => h.1
          | ⟨k + 1, hk⟩ => forall_of_all p.tail h.2 ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    forall_of_all p
    , let rec all_of_forall {n : Nat} (p : Family Prop n) : (∀ k, p k) → p.all :=
      λ h => match n with
        | 0 => ⟨⟩
        | n + 1 => ⟨h ⟨0, n.zero_lt_succ⟩, all_of_forall p.tail λ k => h k.succ⟩
    all_of_forall p⟩

  instance {n : Nat} (p : Family Prop n) [i : ∀ k, Decidable (p k)] : Decidable (∀ k, p k) :=
    let rec r : (n : Nat) → (p : Family Prop n) → (∀ k, Decidable (p k)) → Decidable p.all
      | 0, p, i => isTrue ⟨⟩
      | n + 1, p, i => 
        let i1 : Decidable p.head := i ⟨0, n.zero_lt_succ⟩
        let i2 : Decidable p.tail.all := r n _ λ k => i k.succ
        let this : Decidable (p.head ∧ p.tail.all) := inferInstance
        this
      let this := r n p i
      if c : p.all then isTrue $ p.all_iff_forall.mp c
      else isFalse $ c ∘ p.all_iff_forall.mpr

  instance {n : Nat} (p : Family Prop n) [Decidable (∀ k, ¬p k)] : Decidable (∃ k, p k) :=
    if h : ∀ k, ¬p k then isFalse $ not_exists.mpr h
    else isTrue $ let ⟨x, hx⟩ := not_forall.mp h; ⟨x, not_not.mp hx⟩

  instance {n : Nat} (p : Family Prop n) [Decidable (∀ k, p k)] : Decidable (∃ k, ¬p k) :=
    if h : ∀ k, p k then isFalse $ not_exists.mpr λ k => not_not.mpr (h k)
    else isTrue $ not_forall.mp h
end


section
  def has_fun_dec_eq {α} [DecidableEq α] {n : Nat} (f g : Family α n) : Decidable (f = g) :=
    let dec_eq_lemma {n} {f g : Family α (n + 1)} : f.head = g.head ∧ f.tail = g.tail
      → f = g := 
      λ h => let p := of λ k => f k = g k
        have : ∀ k, p.tail k := λ k => show f.tail _ = g.tail _ from h.2 ▸ rfl
        funext $ p.all_iff_forall.mp ⟨h.1, p.tail.all_iff_forall.mpr this⟩
    match n, f, g with
    | 0, f, g => isTrue $ funext $ f0
    | n + 1, f, g => 
      let this := has_fun_dec_eq f.tail g.tail
      if h : f.head = g.head ∧ f.tail = g.tail then isTrue (dec_eq_lemma h)
      else isFalse λ c => h ⟨c ▸ rfl, funext $ λ k => c ▸ rfl⟩

  instance {α} [DecidableEq α] : DecidableEq (Family α n) := has_fun_dec_eq

  instance {α} {n : Nat} (f g : Family α n) [i : ∀ k, Decidable (f k = g k)] : Decidable (f = g) :=
    let p := of λ k => f k = g k
    let i1 : ∀ k, Decidable (p k) := i
    let i2 : Decidable (∀ k, f k = g k) := show Decidable (∀ k, p k) from inferInstance
    if c : ∀ k, f k = g k then isTrue $ funext $ c
    else isFalse $ λ d => c $ λ k => d ▸ rfl
end


section
  variable {α β} (f : β → α → α) (a : α) in
  def foldr : {n : Nat} → (l : Family β n) → α
    | 0, _ => a
    | n + 1, l => f l.head l.tail.foldr
end


end Family
end Fin
