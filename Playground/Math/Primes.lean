import Mathlib

namespace Nat

structure Divisor (n d : Nat) : Prop where
  divisor : d * (n / d) = n

namespace Divisor
theorem iff : Divisor n d ↔ d * (n / d) = n := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩
instance : Decidable (Divisor n d) := by rw [iff]; apply decEq

structure Proper (n d) extends Divisor n d : Prop where
  proper : d < n
end Divisor

def properDivs (n : Nat) := List.range n |>.filter (decide $ n.Divisor .)

namespace Divisor.Proper
open List

theorem of_mem_properDivs (h : d ∈ n.properDivs) : Proper n d := by
  erw [mem_filter, mem_range, decide_eq_true_iff] at h
  constructor
  . exact h.2
  . exact h.1

theorem to_mem_properDivs (h : Proper n d) : d ∈ n.properDivs := by
  erw [mem_filter, mem_range, decide_eq_true_iff]
  constructor
  . exact h.2
  . exact h.1

theorem iff_mem_properDivs : Proper n d ↔ d ∈ n.properDivs := by
  constructor
  . exact to_mem_properDivs
  . exact of_mem_properDivs

end Divisor.Proper

-- #eval decide (Divisor 1 0)

example : decide (Divisor 1 0) = false := by
  rw [decide_eq_false]
  rw [Divisor.iff]
  decide

theorem properDivs_0_length  : (properDivs 0).length = 0 := rfl
theorem properDivs_1_length  : (properDivs 1).length = 0 := by
  have : decide (Divisor 1 0) = false := by
    rw [decide_eq_false]
    rw [Divisor.iff]
    decide
  show List.length (match decide _ with | true => _ | false => _) = 0
  rw [this]
  rfl

theorem properDivs_length_ge_1_of_ge_2  (hn : n ≥ 2) : n.properDivs.length ≥ 1 := by
  apply List.length_pos_iff_exists_mem.mpr
  exists 1
  rw [←Divisor.Proper.iff_mem_properDivs]
  constructor
  . rw [Divisor.iff, Nat.div_one, Nat.one_mul]
  . exact hn


structure IsPrime (n : Nat) : Prop where
  is_prime : n.properDivs.length = 1

namespace IsPrime
theorem iff : IsPrime n ↔ n.properDivs.length = 1 := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩
instance : Decidable (IsPrime n) := by rw [iff]; apply decEq
end IsPrime


def smallestPrimeDiv (n : Nat) (hn : n ≥ 2) : Nat :=
  if h : IsPrime n then n
  else
    have : 1 < n.properDivs.length := Ne.lt_of_le' (by
      show ¬_ = _
      erw [←IsPrime.iff]
      exact h) $ properDivs_length_ge_1_of_ge_2 hn
    n.properDivs[1]


-- def decomp (n : Nat) :=


-- #eval properDivs 5

-- def IsPrime (n : Nat) := ∀ a, a < n → ∀ b, b < n → a * b ≠ n

-- def decidable_isPrime (n) : Decidable $ IsPrime n := decidableBallLT n _

-- instance (n) : Decidable $ IsPrime n := decidable_isPrime n

-- def decomp (n : Nat) : List Nat :=
--   if h : n.IsPrime then [n]
--   else by
--     dsimp [IsPrime] at h
--     push_neg at h
--     -- let ⟨a, _⟩ := h
--     sorry


end Nat
