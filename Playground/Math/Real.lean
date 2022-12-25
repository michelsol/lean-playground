import Mathlib.Init.ZeroOne
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs

-- class Zero.{u} (α : Type u) where zero : α
-- instance [h : Zero α] : OfNat α (nat_lit 0) where ofNat := h.zero
-- class One.{u} (α : Type u) where zero : α
-- instance [h : One α] : OfNat α (nat_lit 1) where ofNat := h.zero
-- class Inv.{u} (α : Type u) where
--   inv : α → α
-- postfix:100 "⁻¹" => Inv.inv

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
  add_left_neg : ∀ a : R, -a + a = 0
  add_comm : ∀ a b : R, a + b = b + a
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  one_mul : ∀ a : R, 1 * a = a
  mul_left_inv : ∀ a : R, x⁻¹ * a = 1
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

  def natCast : ℕ → ℝ
  | 0 => 0
  | n + 1 => natCast n + 1
  def intCast : ℤ → ℝ
  | .ofNat n => natCast n
  | .negSucc n => -natCast (n + 1)

  instance : AddCommGroup ℝ where
    add_assoc := add_assoc
    add_comm := add_comm
    zero_add := zero_add
    add_zero a := add_comm a _ ▸ zero_add a
    add_left_neg := add_left_neg
  instance : CommRing ℝ where
    mul_assoc := mul_assoc
    one_mul := one_mul
    mul_one a := mul_comm a _ ▸ one_mul a
    zero_mul := zero_mul
    mul_zero a := mul_comm a _ ▸ zero_mul a
    left_distrib a _ _ := 
      mul_comm a _ ▸ right_distrib _ _ a ▸ mul_comm a _ ▸ mul_comm a _ ▸ rfl
    right_distrib := right_distrib
    natCast := natCast
    natCast_zero := rfl
    natCast_succ _ := rfl
    add_left_neg := add_left_neg
    intCast := intCast
    intCast_ofNat _ := rfl
    intCast_negSucc _ := rfl
    mul_comm := mul_comm

  example : AddRightCancelSemigroup ℝ := inferInstance

  example (a b : ℝ) (h : a * b = 0) : a = 0 ∨ b = 0 :=
    sorry

  theorem le_of_le_add_right {a b c : ℝ} (h : a + c ≤ b + c) : a ≤ b :=
    have h := le_add_right_of_le (-c) h
    add_zero a ▸ add_zero b ▸ add_right_neg c ▸ add_assoc a .. ▸ add_assoc b .. ▸ h

  theorem lt_add_right_of_lt {a b : ℝ} (c : ℝ) (h : a < b) : a + c < b + c := by
    apply lt_of_le_of_ne
    . apply le_add_right_of_le
      exact le_of_lt h
    . intro d
      apply ne_of_lt h
      exact add_right_cancel d



  end Real

end
