-- import Mathlib.Tactic.Linarith
-- import Mathlib.Algebra.Module.LinearMap
import Mathlib

-- un espace vectoriel admet une base

example (a : ℤ) (h1 : a ≥ 3) : a ≥ 1 := by
  -- linarith
  sorry


example (X) (s : Set X) : Type := s

example := OrderIso
example := Ordinal
-- example := Quotient

noncomputable def exp_series_term (n : ℕ) (x : ℂ) : ℂ := x ^ n / n.factorial
open BigOperators Finset in
noncomputable def exp_series_partial_sum (N : ℕ) (x : ℂ) : ℂ := ∑ n in range N, exp_series_term n x


open Filter Topology in
theorem tendsto_const {α} (x : Filter α) [NeBot x]
  {β} [TopologicalSpace β] [T1Space β] (l : β)
   : Tendsto (Function.const α l) x (𝓝 l) := by
  rw [Tendsto, ←Function.const_def, Filter.map_const, pure_le_nhds_iff]

open Filter Topology in
theorem tendsto_one_sub_pos_div_one_sub_atTop_of_lt_one (r : ℝ) (h₁ : r ≥ 0) (h₂ : r < 1) 
  : Tendsto (λ n : ℕ => (1 - r ^ n) / (1 - r)) atTop (𝓝 (1/(1 - r))) := by
  apply Filter.Tendsto.div _ _ (by linarith)
  . have : 𝓝 1 = 𝓝 ((1 : ℝ) - 0) := by congr; linarith
    rw [this]
    apply Filter.Tendsto.sub
    . apply tendsto_const
    -- . exact tendsto_pow_atTop_nhds_0_of_lt_1 h₁ h₂
    . sorry
  . apply Filter.Tendsto.sub
    . apply tendsto_const
    . apply tendsto_const

def eq_of_mul_eq_of_ne_zero {a b c : ℝ} (ha : a ≠ 0) (h : b * a = c * a) : b = c := by
  rw [←mul_div_cancel b ha, ←mul_div_cancel c ha]
  congr


open BigOperators Finset in
def Finset.sum_range_pow_eq (n : ℕ) (x : ℝ) (hx : x ≠ 1) : ∑ k in range n, x ^ k = (1 - x ^ n) / (1 - x) := by
  induction n with
  | zero => simp_arith
  | succ n ih => 
    rw [sum_range_succ, ih]
    have : 1 - x ≠ 0 := λ c => hx $ by linarith
    apply eq_of_mul_eq_of_ne_zero this
    . rw [right_distrib, div_mul_cancel _ this, div_mul_cancel _ this, mul_sub_left_distrib]
      ring_nf
      sorry



example (x : ℝ) : deriv (λ t => t * t) x = 2 * x := by
rw [deriv_mul differentiableAt_id differentiableAt_id, 
    congrFun deriv_id'' x, one_mul, mul_one, two_mul]


local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)
-- local macro_rules | `($x * $y)   => `(HMul.hMul $x $y)


theorem th (n : ℕ) (x : ℝ) : deriv (λ t : ℝ => t ^ (n + 1)) x = (n + 1 : ℕ) * (x ^ n) := by
  induction n with
  | zero => 
    rw [Nat.zero_add, pow_zero, Nat.cast_one, one_mul]
    apply Eq.trans _ (deriv_id x)
    congr
    funext t
    rw [pow_one]
    rfl
  | succ n hn => 
    sorry


theorem t0 : ∫ x : ℝ in Set.Icc 0 10, (1 : ℝ) = 10 := by 
let f : ℝ → ℝ := λ _ => 1
show MeasureTheory.integral _ f = _
rw [MeasureTheory.integral_eq f _]
. 
  -- library_search
  sorry
. 
  exact MeasureTheory.integrable_const 1
-- #print t0



-- theorem aaa (n : ℕ) : (n + (1 : ℝ)) = ((Nat.add n 1) : ℝ) := 
--   by
--   rw [←Nat.cast_one, ←Nat.cast_add]
-- #print aaa
-- theorem th1 (a : ℝ) (n : ℕ) : Real.rpow a n = Monoid.npow n a := by
-- rw [Real.rpow_nat_cast]
-- #print th1

example {α β} (f : α → β) : α → Inhabited β := λ x => ⟨f x⟩

example {α β} (g : α → Inhabited β) : α → β := λ x => (g x).default
