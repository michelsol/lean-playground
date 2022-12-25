import Mathlib

-- some goals can be proven directly by linarith / nlinarith

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)
-- local macro_rules | `($x * $y)   => `(HMul.hMul $x $y)

example {a b : ℝ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 := calc
  (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
  _ = (4 : ℝ) ^ 2 + 4 * 1 := by rw [h1, h2]
  _ = 20 := by norm_num

example {a b : ℝ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := calc
  a = 2 * 3 + 5 := by rwa [←h2]
  _ = 11 := by norm_num

example {x : ℝ} (h1 : x + 4 = 2) : x = -2 := by
  linarith

example {a b : ℝ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + (3 : ℝ) = (4 : ℝ) * b ^ 2 + 10 * b + 9 :=
  by
  -- nlinarith
  sorry

example {a b : ℝ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
  3 * a * b + a ≤ 7 * b + 72 :=
calc
  (3 : ℝ) * a * b + a
    ≤ (2 : ℝ) * b ^ 2 + a ^ 2 + (3 * a * b + a) := by
      apply le_add_of_nonneg_of_le ?_ (le_refl _)
      apply add_nonneg ?_ ?_
      . rw [two_mul]
        apply add_nonneg ?_1 ?_1
        exact sq_nonneg b
      . exact sq_nonneg a
  _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring
  _ ≤ 2 * (8 * b) + 8 * a + a := by 
    apply add_le_add ?_ (le_refl _)
    apply add_le_add ?_ ?_
    . apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact mul_le_mul_of_nonneg_right h3 h2
    . exact mul_le_mul_of_nonneg_right h3 h1
  _ = 7 * b + 9 * (a + b) := by ring
  _ ≤ 7 * b + 9 * 8 := by
    apply add_le_add (le_refl _) ?_
    apply mul_le_mul_of_nonneg_left h3 (by norm_num)
  _ = 7 * b + 72 := by norm_num


example : ¬ ∃ f : X → Set X, f.Surjective := by
  intro ⟨f, hf⟩
  let s := { x | x ∉ f x }
  let ⟨a, ha⟩ := hf s
  by_cases h : a ∈ s
  · have h : a ∉ f a := h
    rw [ha] at h
    contradiction
  · have h : ¬ a ∉ f a := h
    rw [ha] at h
    contradiction

#check Acc.rec



example {α} (s : α → Bool) (x : α) : Decidable (s x = true) :=
match s x with
| true => isTrue rfl
| false => isFalse $ λ c => sorry

theorem problem1 {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 := by
  suffices n^2 - 2 * n - 11 > 0 from by linarith
  calc
    n^2 - (2 : ℤ) * n - (11 : ℤ) = (n - 1)^2 - 12 := by linarith
    _ ≥ (4 : ℤ)^2 - 12 := by
      suffices (n - 1)^2 ≥ (4 : ℤ)^2 from by linarith
      apply pow_le_pow_of_le_left _ (by linarith) 2
      decide
    _ > 0 := by decide
