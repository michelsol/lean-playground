import Mathlib.Init.Logic
import Std.Data.Nat.Lemmas

namespace Old
def mod.F
(a : Nat) (mod_r : (y : Nat) → y < a → (b : Nat) → b > 0 → Nat)
(b : Nat) (hb : b > 0)
: Nat :=
if h : a < b then a
else have h : b ≤ a := Nat.le_of_not_lt h
  have : a - b < a := Nat.sub_lt (Nat.lt_of_lt_of_le hb h) hb
  mod_r (a - b) this b hb

def mod : (a b : Nat) → (hb : b > 0) → Nat := 
WellFounded.fix' (measure id).wf mod.F

theorem mod_fix_eq (a b : Nat) (hb : b > 0)
: mod a b hb = mod.F a (λ y _ b => mod y b) b hb := 
WellFounded.fix_eq (measure id).wf mod.F a ▸ rfl

theorem mod_th (a b : Nat) (hb : b > 0) : mod (a + b) b hb = mod a b hb :=
(mod_fix_eq (a + b) b hb ▸
show ite .. = _ from
have : ¬ a + b < b := Nat.not_lt_of_le (b.le_add_left a)
if_neg this ▸ Nat.add_sub_cancel .. ▸ rfl)

end Old

namespace New

def mod (a b : Nat) (hb : b > 0) : Nat :=
if h : a < b then a
else have h : b ≤ a := Nat.le_of_not_lt h
  -- have : a - b < a := Nat.sub_lt (Nat.lt_of_lt_of_le hb h) hb
  mod (a - b) b hb
termination_by _ => a
decreasing_by (simp_wf; exact Nat.sub_lt (Nat.lt_of_lt_of_le hb h) hb)

theorem mod_th (a b : Nat) (hb : b > 0) : mod (a + b) b hb = mod a b hb :=
sorry

end New
