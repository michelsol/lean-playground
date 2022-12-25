import Playground.Data.Bool.Basic

namespace List

theorem all_of_forall {α} {l : List α} {p : α → Prop} [DecidablePred p]
: (∀ x ∈ l, p x) → (l.all λ x => decide (p x)) = true
:= λ h => match l with
| [] => rfl
| a :: l => Bool.and_of_true
  (decide_eq_true (h a (Mem.head l)))
  (all_of_forall λ x hx => h x (Mem.tail a hx))

theorem forall_of_all {α} {l : List α} {p : α → Prop} [DecidablePred p]
: (l.all λ x => decide (p x)) = true → (∀ x ∈ l, p x)
:= λ h => match l with
| [] => λ x hx => nomatch hx
| a :: l => λ x hx => match hx with
  | Mem.head .. => of_decide_eq_true (Bool.and_left h)
  | Mem.tail _ hx => forall_of_all (Bool.and_right h) x hx

end List
