namespace Fin
section
  def f0 {α : Fin 0 → Sort _} : (k : _) → α k
    | k => False.elim (Nat.not_lt_zero _ k.isLt)

  def f1 {α : Fin 1 → Sort _} : Inhabited (α 0) → (k : _) → α k
    | ⟨a⟩, 0 => a

  def f2 {α : Fin 2 → Sort _} : PProd (α 0) (α 1) → (k : _) → α k
    | ⟨a, b⟩, 0 => a
    | ⟨a, b⟩, 1 => b

  structure PProd3 (α : Sort u) (β : Sort v) (γ : Sort w) where
    fst : α
    snd : β
    thd : γ

  def f3 {α : Fin 3 → Sort _} : PProd3 (α 0) (α 1) (α 2) → (k : _) → α k
    | ⟨a, b, c⟩, 0 => a
    | ⟨a, b, c⟩, 1 => b
    | ⟨a, b, c⟩, 2 => c

  def as_succ (x : Fin n) : Fin (n + 1) := ⟨x.val, Nat.lt_trans x.isLt n.lt_succ_self⟩
end
end Fin