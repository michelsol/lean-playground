import Mathlib

namespace Nat

def Divisor (n d : Nat) := d * (n.div d) = n
instance : Decidable (Divisor n d) := decEq ..

def properDivs (n : Nat) := List.range n |>.filter (decide $ n.Divisor .)

namespace Divisor
section
open List
variable {n d : Nat}

theorem of_mem_properDivs (h : d ∈ n.properDivs) : Divisor n d := by
  erw [mem_filter, decide_eq_true_iff] at h
  exact h.2

def dividend (_ : Divisor n d) := n
def val (_ : Divisor n d) := d
end

def Proper (_ : Divisor n d) := d < n

namespace Proper
section
open List
variable {hd : Divisor n d}

theorem of_mem_properDivs (h : d ∈ n.properDivs) : (of_mem_properDivs h).Proper := by
  erw [mem_filter, mem_range] at h
  exact h.1

theorem to_mem_properDivs (h : hd.Proper) : hd.val ∈ hd.dividend.properDivs := by
  erw [mem_filter, decide_eq_true_iff, mem_range]
  exact ⟨h, hd⟩

theorem iff : hd.Proper ↔ hd.val ∈ hd.dividend.properDivs := by
  constructor
  . exact to_mem_properDivs
  . exact of_mem_properDivs

end
end Proper
end Divisor



def IsPrime (n : Nat) := n.properDivs.length = 1
instance : DecidablePred IsPrime := λ _ => decEq ..

-- def smallestPrimeDiv (n : Nat) :=
--   n.properDivs[1]

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
