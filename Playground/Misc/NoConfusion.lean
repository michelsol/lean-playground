

section

-- set_option pp.all true
-- #print Nat.casesOn
#print Nat.zero
#print Nat.succ
#print Nat.rec

#print Nat.noConfusionType
#print Nat.noConfusion


def Nat.noConfusionType2 : Sort u → Nat → Nat → Sort u
| P, zero, zero => P → P
| P, zero, succ m => P
| P, succ n, zero => P
| P, succ n, succ m => (n = m → P) → P
def Nat.noConfusion2 {P : Sort u} {n m} (h : n = m) : noConfusionType2 P n m :=
match n with
| zero => h ▸ λ g => g
| succ n => h ▸ λ g => g rfl


noncomputable def Nat.rec3 : {motive : Nat → Sort u} 
→ motive zero → ((n : Nat) → motive n → motive (succ n)) → (t : Nat) → motive t
:= Nat.rec
noncomputable def Nat.casesOn3 {motive : Nat → Type}
  (t : Nat) (z : motive Nat.zero) (h : (n : Nat) → motive (Nat.succ n)) : motive t :=
  rec3 z (λ n ih => h n) t
noncomputable def Nat.casesOn3' {motive : Nat → Prop}
  (t : Nat) (z : motive Nat.zero) (h : (n : Nat) → motive (Nat.succ n)) : motive t :=
  rec3 z (λ n ih => h n) t
noncomputable def Nat.noConfusionProp3 : Nat → Nat → Prop := 
λ n m => casesOn3 (motive := λ _ => Prop) n
  (casesOn3 (motive := λ _ => Prop) m True (λ m => False))
  (λ n => casesOn3 (motive := λ _ => Prop) m False (λ m => n = m))
theorem Nat.noConfusion3
{n m : Nat} : n = m → noConfusionProp3 n m
 :=
casesOn3' (motive := λ n => n = m → noConfusionProp3 n m) n
  (λ h => h ▸ trivial)
  (λ n h => h ▸ rfl)


theorem Nat.lemma1 : ∀ n m, succ n = succ m → n = m := 
λ n m => noConfusion3



theorem Nat.aaa : zero ≠ succ zero := noConfusion2
theorem Nat.bbb (h : succ n = succ m) : n = m := noConfusion2 h id

end

section

class Is_Nat_Type (Is_Nat : Type → Prop) where
  zero : Type
  zero_is_nat : Is_Nat zero
  succ (x : Type) (hx : Is_Nat x) : Type
  succ_is_nat : ∀ x hx, Is_Nat $ succ x hx

class Is_Nat (x : Type) : Prop
local instance : Is_Nat_Type Is_Nat := sorry
def nat_succ (x : Type) [hx : Is_Nat x] : {y // Is_Nat y} := ⟨Is_Nat_Type.succ x hx, Is_Nat_Type.succ_is_nat ..⟩


end