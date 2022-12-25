import Mathlib.Algebra.Group.Defs

section

  def Array.cons {α} (x : α) (a : Array α) : Array α := mk (x :: a.data)

  infixr:67 " ::# " => Array.cons

  theorem Array.recursion {α}
  {motive : Array α → Sort v}
  (h0 : motive #[])
  (ih : (a : Array α) → (x : α) → motive a → motive (x ::# a))
  (a : Array α)
  : motive a := 
  let motive' : List α → Sort v := λ l => motive (mk l)
  show motive' a.data from
  List.rec h0 (λ x l h => ih (mk l) x h) a.data

  @[simp]
  theorem Array.forIn_cons {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (f : α → β → m (ForInStep β))
  (a : α) (as : Array α) (b : β)
  : (forIn (a ::# as) b f)
      = (do match (<- f a b) with
        | ForInStep.done b => pure b
        | ForInStep.yield b => forIn as b f) := by
    show (do match (<- f ((a ::# as).get ⟨as.size - as.size, (as.size.sub_self ▸ as.size.zero_lt_succ) ⟩) b) with
            | ForInStep.done b => pure b
            | ForInStep.yield b => forIn.loop (a ::# as) f as.size as.size.le_succ b)
      =  (do match (<- f a b) with
            | ForInStep.done b => pure b
            | ForInStep.yield b => forIn as b f : m β)
    suffices ((a ::# as).get ⟨as.size - as.size, (as.size.sub_self ▸ as.size.zero_lt_succ) ⟩) = a from by
      rw [this]
      apply congrArg; apply funext; intro r
      apply congrArg; apply funext; exact forIn_loop_cons_eq
    simp; rfl
  where
    forIn_loop_cons_eq : ∀ b : β, (forIn.loop (a ::# as) f as.size (Nat.le_succ as.size) b)
      = forIn.loop as f as.size (Nat.le_refl _) b :=
        forIn_loop_cons_eq_lemma as.size (Nat.le_refl _)
    forIn_loop_cons_eq_lemma (i : Nat) (hi : i ≤ as.size)
    : ∀ b : β, (forIn.loop (a ::# as) f i (Nat.le_trans hi as.size.le_succ) b)
      = forIn.loop as f i hi b := by induction i with
    | zero => intro b; rfl
    | succ i ih =>
      intro b
      have ih := ih (Nat.le_trans i.le_succ hi)
      show  (do match (<- f ((a ::# as).get ⟨(a ::# as).size - 1 - i, _⟩) b) with
            | ForInStep.done b => pure b
            | ForInStep.yield b => forIn.loop (a ::# as) f i _ b : m β) =
            (do match (<- f (as.get ⟨as.size - 1 - i, _⟩) b) with
            | ForInStep.done b => pure b
            | ForInStep.yield b => forIn.loop as f i _ b : m β)
      suffices (f ((a ::# as).get ⟨(a ::# as).size - 1 - i, _⟩) b)
          = (f (as.get ⟨as.size - 1 - i, _⟩) b) from by
        rw [this]
        apply congrArg; apply funext; intro r
        apply congrArg; apply funext; exact ih
      apply congrArg (f . _)
      have : as.size - 1 - i + 1 < as.size + 1 := by
        cases h : as.size with
        | zero => rw [h] at hi; contradiction
        | succ k => exact Nat.succ_lt_succ (Nat.succ_le_succ (Nat.sub_le k i))
      show (a ::# as).get _ = (a ::# as).get ⟨_, this⟩
      apply congrArg
      suffices (a ::# as).size - 1 - i = as.size - 1 - i + 1 from by simp [this]
      show as.size + 1 - 1 - i = as.size - 1 - i + 1
      rw [Nat.add_comm, Nat.add_sub_assoc, Nat.add_sub_assoc, Nat.add_comm]
      . exact Nat.le_pred_of_lt hi
      . exact Nat.le_trans i.zero_lt_succ hi

end

section
  class Cons (ρ : Type u) (α : outParam (Type v)) where
    cons : α → ρ → ρ

  class ForIn_Cons (m : Type u₁ → Type u₂) (ρ : Type u) (α : Type v)
    [Monad m] [Cons ρ α] [ForIn m ρ α] 
    where
    forIn_cons {β} (f : α → β → m (ForInStep β)) (a : α) (as : ρ) (b : β)
      : forIn (Cons.cons a as) b f
      = f a b >>= λ | ForInStep.done b => pure b | ForInStep.yield b => forIn as b f

  instance {α} : Cons (List α) α where
    cons := List.cons

  instance {α} : Cons (Array α) α where
    cons := Array.cons

  instance {α} {m} [Monad m] : ForIn_Cons m (List α) α where
    forIn_cons := List.forIn_cons

  instance {α} {m} [Monad m] : ForIn_Cons m (Array α) α where
    forIn_cons := Array.forIn_cons

end


section
  variable {α : Type u} [AddCommSemigroup α]

  namespace List

  def sum (l : List α) (x₀ : α) : α := 
    match l with
    | [] => x₀
    | x :: l => l.sum x₀ + x

  def iter_sum (l : List α) (x₀ : α) : α :=
    Id.run do
      let mut s := x₀
      for x in l do
        s := s + x
      return s

  theorem iter_sum_cons_add (l : List α) 
  : ∀ x₀ x : α, (x :: l).iter_sum x₀ = l.iter_sum x₀ + x := by
    induction l with
    | nil => exact λ _ _ => rfl
    | cons y l hl =>
      intro x₀ x
      show l.iter_sum (x₀ + x + y) = l.iter_sum (x₀ + y) + x
      rw [←hl]
      show l.iter_sum (x₀ + x + y) = l.iter_sum (x₀ + y + x)
      apply congrArg l.iter_sum
      rw [add_assoc, add_assoc, add_comm x y]

  theorem iter_sum_eq_sum (l : List α) (x₀ : α)
    : l.iter_sum x₀ = l.sum x₀ :=
    match l with
    | [] => rfl
    | x :: l => l.iter_sum_cons_add x₀ x ▸ l.iter_sum_eq_sum x₀ ▸ rfl

  end List

  namespace Array

  def iter_sum (a : Array α) (x₀ : α) : α :=
    Id.run do
      let mut s := x₀
      for x in a do
        s := s + x
      return s

  theorem iter_sum_cons_add 
  : ∀ a : Array α, ∀ x₀ x, (x ::# a).iter_sum x₀ = a.iter_sum x₀ + x := 
    recursion (λ _ _ => rfl) <| by
    intro a y ha
    intro x₀ x
    simp [iter_sum]; show a.iter_sum (x₀ + x + y) = a.iter_sum (x₀ + y) + x
    rw [←ha]
    simp [iter_sum]; show a.iter_sum (x₀ + x + y) = a.iter_sum (x₀ + y + x)
    apply congrArg a.iter_sum
    rw [add_assoc, add_assoc, add_comm x y]

  end Array

  section
  variable {α : Type _} [Add α]
  variable {ρ} [∀ m, ForIn m ρ α] [Cons ρ α] [∀ m, [Monad m] → ForIn_Cons m ρ α]
  def iter_sum (a : ρ) (x₀ : α) : α :=
    Id.run do
      let mut s := x₀
      for x in a do
        s := s + x
      return s
  end

end