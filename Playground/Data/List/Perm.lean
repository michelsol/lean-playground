import Std.Data.List.Lemmas
import Mathlib.Data.List.Perm

section
  namespace List
  variable {type}

  theorem Perm.append_right {l₁ l₂ : List type} (r : List type) : l₁ ~ l₂ → l₁ ++ r ~ l₂ ++ r
  := λ h => match r with
  | [] => append_nil .. ▸ append_nil .. ▸ h
  | a :: r => (perm_middle.trans ((h.append_right r).cons a)).trans perm_middle.symm

  theorem Perm.append_left {r₁ r₂ : List type} (l : List type) : r₁ ~ r₂ → l ++ r₁ ~ l ++ r₂
  := λ h => match l with
  | [] => h
  | a :: l => (h.append_left l).cons a


  end List
end