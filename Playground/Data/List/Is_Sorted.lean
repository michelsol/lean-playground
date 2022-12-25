import Std.Data.List.Lemmas
import Mathlib.Init.Order.Defs

section
  namespace List
  variable {type} [LinearOrder type]

  def IsSorted : List type → Prop
  | [] => True
  | a :: [] => True
  | a :: b :: l => a ≤ b ∧ (b :: l).IsSorted

  theorem snoc_snoc_IsSorted_iff {l : List type} {y z : type}
  : (l ++ [y] ++ [z]).IsSorted ↔ (l ++ [y]).IsSorted ∧ y ≤ z
  := match l with
  | [] => by simp [IsSorted]
  | a :: [] => by simp [IsSorted]
  | a :: b :: l => by 
    show _ ∧ (b :: l ++ [y] ++ [z]).IsSorted ↔ (_ ∧ (b :: l ++ [y]).IsSorted) ∧ _
    rw [and_assoc, snoc_snoc_IsSorted_iff]

  theorem append_cons_IsSorted_iff {l r : List type} {v : type}
  : (l ++ v :: r).IsSorted ↔ (l ++ [v]).IsSorted ∧ (v :: r).IsSorted
  := match r with
  | [] => ⟨λ h => ⟨h, ⟨⟩⟩, λ h => h.1⟩
  | b :: r => by
    rw [append_cons, append_cons_IsSorted_iff]
    show _ ↔ _ ∧ (_ ∧ _)
    rw [snoc_snoc_IsSorted_iff, and_assoc]

  theorem snoc_IsSorted_iff_IsSorted_and_forall_le {l : List type} {z : type}
  : (l ++ [z]).IsSorted ↔ l.IsSorted ∧ ∀ x ∈ l, x ≤ z
  := match l with
  | [] => by simp [IsSorted]
  | a :: [] => 
    ⟨λ h => ⟨trivial, λ x hx => mem_singleton.mp hx ▸ h.1⟩, λ h => ⟨h.2 a (mem_singleton.mpr rfl), trivial⟩⟩
  | a :: b :: l => by
    show _ ∧ (b :: l ++ [z]).IsSorted ↔ (_ ∧ (b :: l).IsSorted) ∧ _
    rw [and_assoc, snoc_IsSorted_iff_IsSorted_and_forall_le]
    exact ⟨λ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, λ x hx => match hx with
      | Mem.head _ => le_trans h₁ (h₃ b (Mem.head ..))
      | Mem.tail _ hx => h₃ x hx⟩
      , λ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, λ x hx => h₃ x (Mem.tail _ hx)⟩⟩

  theorem cons_IsSorted_iff_IsSorted_and_forall_le {l : List type} {a : type}
  : (a :: l).IsSorted ↔ l.IsSorted ∧ ∀ x ∈ l, a ≤ x
  := match l with
  | [] => by simp [IsSorted]
  | b :: l => by
    show _ ∧ _ ↔ _
    rw [cons_IsSorted_iff_IsSorted_and_forall_le]
    exact ⟨λ ⟨h₁, h₂, h₃⟩ => ⟨⟨h₂, h₃⟩, λ x hx => le_trans h₁ $ match hx with
      | Mem.head _ => le_refl x 
      | Mem.tail _ hx => h₃ x hx⟩
    , λ ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨h₃ b (Mem.head ..), h₁, h₂⟩⟩

  theorem append_cons_IsSorted_iff_left_IsSorted_and_forall_le_and_right_IsSorted_and_forall_ge 
  {l r : List type} {v : type}
  : (l ++ v :: r).IsSorted ↔ (l.IsSorted ∧ ∀ x ∈ l, x ≤ v) ∧ (r.IsSorted ∧ ∀ x ∈ r, v ≤ x)
  := by
    rw [←snoc_IsSorted_iff_IsSorted_and_forall_le]
    rw [←cons_IsSorted_iff_IsSorted_and_forall_le]
    rw [append_cons_IsSorted_iff]


  end List
end