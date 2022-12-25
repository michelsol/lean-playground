import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Playground.Data.Fin.Family.Basic

namespace Fin.Family
section
  def sum {α n} [Add α] (a : α) (l : Family α n) : α := foldr Add.add a l

  theorem sum_eq_add_sum {α n} [Add α] (a : α) (l : Family α (n + 1)) 
  : l.sum a = l.head + l.tail.sum a := rfl

  theorem sum_ge {n} (l : Family ℕ n) : ∀ k, l.sum 0 ≥ l k :=
    match n with
    | 0 => f0
    | n + 1 => λ k => match k with
      | ⟨0, _⟩ => show l.head + l.tail.sum _ ≥ l.head from Nat.le_add_right l.head _
      | ⟨k + 1, c⟩ =>
        have := l.tail.sum_ge ⟨k, Nat.lt_of_succ_lt_succ c⟩
        show l.head + l.tail.sum _ ≥ l.tail ⟨k, Nat.lt_of_succ_lt_succ c⟩ from
        (Nat.zero_add (l.tail _)).symm ▸ Nat.add_le_add (Nat.zero_le _) this

  theorem sum_add_eq_add_sum {α n} [CommSemiring α] (f g : Family α n)
  : (of λ i => f i + g i).sum 0 = f.sum 0 + g.sum 0 :=
    match n with
    | 0 => (zero_add (0 : α)).symm ▸ rfl
    | n + 1 => 
      show (f.head + g.head) + (of λ i => f i + g i).tail.sum 0 
        = f.head + f.tail.sum 0 + (g.head + g.tail.sum 0) from
      sum_add_eq_add_sum f.tail g.tail ▸ by ring
end
end Fin.Family