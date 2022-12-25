import Mathlib.Init.ZeroOne
import Mathlib.Init.Order.Defs
-- import Mathlib.Algebra.Group.Defs
-- import Mathlib.Algebra.Ring.Defs

-- class Zero.{u} (α : Type u) where zero : α
-- instance [h : Zero α] : OfNat α (nat_lit 0) where ofNat := h.zero
-- class One.{u} (α : Type u) where zero : α
-- instance [h : One α] : OfNat α (nat_lit 1) where ofNat := h.zero
class Inv.{u} (α : Type u) where
  inv : α → α
postfix:100 "⁻¹" => Inv.inv

class Real_Data.{u} (R : Type u)
extends Add R, Neg R, Zero R, Mul R, Inv R, One R

instance {R} [Real_Data R] : Sub R where
  sub a b := a + (-b)
instance {R} [Real_Data R] : Div R where
  div a b := a * b⁻¹

class Real (R)
extends Real_Data R, LinearOrder R
where
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  zero_add : ∀ a : R, 0 + a = a
  neg_add : ∀ a : R, -a + a = 0
  add_comm : ∀ a b : R, a + b = b + a
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  one_mul : ∀ a : R, 1 * a = a
  inv_mul : ∀ a : R, a⁻¹ * a = 1
  mul_comm : ∀ a b : R, a * b = b * a
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c
  zero_mul : ∀ a : R, 0 * a = 0
  le_add_right_of_le : ∀ {a b : R} (c : R), a ≤ b → a + c ≤ b + c
  zero_le_mul_of_zero_le : ∀ {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b

class Reals where
  reals : Type
  reals_are_real : Real reals
notation:max "ℝ" => Reals.reals
instance [Reals] : Real ℝ := Reals.reals_are_real

section
  variable [Reals]

  namespace Real

  attribute [simp] zero_add neg_add one_mul inv_mul zero_mul right_distrib

  def natCast : ℕ → ℝ
  | 0 => 0
  | n + 1 => natCast n + 1
  def intCast : Int → ℝ
  | .ofNat n => natCast n
  | .negSucc n => -natCast (n + 1)

  example (a b : ℝ) (h : a * b = 0) : a = 0 ∨ b = 0 :=
    sorry

  @[simp] theorem add_zero (a : ℝ) : a + 0 = a := by rw [add_comm, zero_add]
  @[simp] theorem add_neg (a : ℝ) : a + -a = 0 := by rw [add_comm, neg_add]
  theorem sub_eq_add_neg (a b : ℝ) : a - b = a + -b := rfl

  theorem eq_add_right_of_eq {a b : ℝ} (c : ℝ) (h : a = b) : a + c = b + c := by rw [h]
  theorem eq_of_eq_add_right {a b c : ℝ} (h : a + c = b + c) : a = b := by
    have h := eq_add_right_of_eq (-c) h
    rw [add_assoc, add_assoc, add_neg, add_zero, add_zero] at h
    exact h
  @[simp] theorem eq_add_right_iff (a b c : ℝ) : a + c = b + c ↔ a = b :=
    ⟨eq_of_eq_add_right, eq_add_right_of_eq c⟩

  theorem le_of_le_add_right {a b c : ℝ} (h : a + c ≤ b + c) : a ≤ b := by
    have h := le_add_right_of_le (-c) h
    rw [add_assoc, add_assoc, add_neg, add_zero, add_zero] at h
    exact h
  @[simp] theorem le_add_right_iff (a b c : ℝ) : a + c ≤ b + c ↔ a ≤ b :=
    ⟨le_of_le_add_right, le_add_right_of_le c⟩

  theorem lt_add_right_of_lt {a b : ℝ} (c : ℝ) (h : a < b) : a + c < b + c := by
    apply lt_of_le_of_ne
    . apply le_add_right_of_le
      exact le_of_lt h
    . intro d
      apply ne_of_lt h
      exact eq_of_eq_add_right d
  theorem lt_of_lt_add_right {a b c : ℝ} (h : a + c < b + c) : a < b := by
    have h := lt_add_right_of_lt (-c) h
    rw [add_assoc, add_assoc, add_neg, add_zero, add_zero] at h
    exact h
  @[simp] theorem lt_add_right_iff (a b c : ℝ) : a + c < b + c ↔ a < b :=
    ⟨lt_of_lt_add_right, lt_add_right_of_lt c⟩


  theorem nonneg_sub_of_le {a b : ℝ} (h : a ≤ b) : 0 ≤ b - a := by
    have h := le_add_right_of_le (-a) h
    rw [add_neg] at h
    exact h
  theorem le_of_nonneg_sub {a b : ℝ} (h : 0 ≤ b - a) : a ≤ b := by
    rw [←le_add_right_iff _ _ (-a)]
    rw [add_neg]
    exact h


  theorem neg_mul_map_left (a b : ℝ) : -(a * b) = -a * b := by
    rw [←eq_add_right_iff _ _ (a * b)]
    rw [neg_add, ←right_distrib, neg_add, zero_mul]

  theorem le_mul_right_of_le (a b c : ℝ) (hc : c ≥ 0) (hab : a ≤ b) : a * c ≤ b * c := by
    rw [←le_add_right_iff _ _ (-(a * c))]
    rw [add_neg]
    rw [neg_mul_map_left]
    rw [←right_distrib]
    exact zero_le_mul_of_zero_le (nonneg_sub_of_le hab) hc




  end Real

end
