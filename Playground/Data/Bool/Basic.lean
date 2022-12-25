import Mathlib.Logic.Basic

namespace Bool

section

theorem and_of_true {p q} (hp : p = true) (hq : q = true) : (p && q) = true
:= hp.symm ▸ hq.symm ▸ rfl

theorem and_left : {p q : Bool} → (p && q) = true → p = true
| true, _, _ => rfl
| false, _, h => false_and _ ▸ h

theorem and_right : {p q : Bool} → (p && q) = true → q = true
| _, true, _ => rfl
| _, false, h => and_false _ ▸ h

end

end Bool


-- section
-- instance (p : Fin k → Prop) [Decidable (∀ k, ¬p k)] : Decidable (∃ k, p k) :=
--   if h : ∀ k, ¬p k then isFalse $ not_exists.mpr h
--   else isTrue $ let ⟨x, hx⟩ := not_forall.mp h; ⟨x, of_not_not hx⟩
-- end