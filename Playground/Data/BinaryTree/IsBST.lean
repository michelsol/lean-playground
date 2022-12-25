import Playground.Data.BinaryTree.Basic
import Playground.Data.List.Is_Sorted
import Mathlib.Data.List.Perm
import Mathlib.Init.Order.Defs

namespace Data.BinaryTree

section
  variable {type} [LinearOrder type]

  inductive IsBST : BinaryTree type → Prop
  | nil : nil.IsBST
  | node {value left right}
    (left_IsBST : left.IsBST) (left_le : ∀ x ∈ left, x ≤ value) 
    (right_IsBST : right.IsBST) (right_ge : ∀ x ∈ right, value ≤ x) 
    : (node value left right).IsBST

  theorem IsBST_iff (value : type) (left right) : (node value left right).IsBST ↔
    (left.IsBST ∧ ∀ x ∈ left, x ≤ value) ∧ (right.IsBST ∧ ∀ x ∈ right, value ≤ x) := by
    constructor
    . intro h; cases h with | node _ _ _ _ =>
      constructor
      . constructor; assumption; assumption
      . constructor; assumption; assumption
    . intro ⟨⟨_, _⟩, ⟨_, _⟩⟩
      apply IsBST.node; assumption; assumption; assumption; assumption

  theorem IsBST_iff_infixList_IsSorted (tree : BinaryTree type)
    : tree.IsBST ↔ tree.infixList.IsSorted := by
    induction tree with
    | nil => 
      constructor
      . intro _; constructor
      . intro _; constructor
    | node value left right left_rec right_rec =>
      rw [IsBST_iff]
      show _ ↔ (left.infixList ++ value :: right.infixList).IsSorted
      rw [List.append_cons_IsSorted_iff_left_IsSorted_and_forall_le_and_right_IsSorted_and_forall_ge]
      rw [left_rec, left.forall_iff_forall_infixList]
      rw [right_rec, right.forall_iff_forall_infixList]
end

section
  variable {type} [LinearOrder type]

  def insertAsInBST (tree : BinaryTree type) (x : type) : BinaryTree type
  := match tree with
  | nil => node x nil nil
  | node value left right =>
      if x ≤ value then node value (left.insertAsInBST x) right
      else node value left (right.insertAsInBST x)

  theorem Mem_insertAsInBST_iff (tree : BinaryTree type) (v : type) (x : type)
  : x ∈ tree.insertAsInBST v ↔ x ∈ tree ∨ x = v
  := match tree with
  | nil => ⟨λ (.eq hx) => .inr hx, λ (.inr hx) => .eq hx⟩
  | node value left right =>
  have left_rec : x ∈ _ ↔ x ∈ _ ∨ x = v := left.Mem_insertAsInBST_iff _ _
  have right_rec : x ∈ _ ↔ x ∈ _ ∨ x = v := right.Mem_insertAsInBST_iff _ _
  show x ∈ ite .. ↔ _ from
  if h_v : v ≤ value then if_pos h_v ▸ ⟨
      λ | .eq hx => .inl (Mem.eq hx)
        | .left hx => match left_rec.mp hx with
          | .inl hx => .inl hx.left
          | .inr hx => .inr hx
        | .right hx => .inl hx.right
    , λ | .inl hx => match hx with
          | .eq hx => .eq hx
          | .left hx => .left $ left_rec.mpr $ .inl hx
          | .right hx => hx.right
        | .inr hx => .left $ left_rec.mpr $ .inr hx⟩
  else if_neg h_v ▸ ⟨
      λ | .eq hx => .inl (Mem.eq hx)
        | .left hx => .inl hx.left
        | .right hx => match right_rec.mp hx with
          | .inl hx => .inl hx.right
          | .inr hx => .inr hx
    , λ | .inl hx => match hx with
          | .eq hx => .eq hx
          | .left hx => hx.left
          | .right hx => .right $ right_rec.mpr $ .inl hx
        | .inr hx => .right $ right_rec.mpr $ .inr hx⟩

  theorem insertAsInBST_IsBST_of_IsBST {tree : BinaryTree type} (h_tree : tree.IsBST) (x : type)
  : (tree.insertAsInBST x).IsBST
  := match tree, h_tree with
  | nil, _ => .node .nil (λ _ => λ.) .nil (λ _ => λ.)
  | node value left right, 
    .node left_IsBST left_le right_IsBST right_ge => 
    show IsBST (ite ..) from
    if h_value : x ≤ value then if_pos h_value ▸ 
      have left_IsBST := left.insertAsInBST_IsBST_of_IsBST left_IsBST x
      have left_le := λ x hx => match (left.Mem_insertAsInBST_iff ..).mp hx with
        | .inl hx => left_le x hx
        | .inr hx => hx ▸ h_value
      .node left_IsBST left_le right_IsBST right_ge
    else if_neg h_value ▸
      have h_value := le_of_lt (lt_of_not_ge h_value)
      have right_IsBST := right.insertAsInBST_IsBST_of_IsBST right_IsBST x
      have right_ge := λ x hx => match (right.Mem_insertAsInBST_iff ..).mp hx with
        | .inl hx => right_ge x hx
        | .inr hx => hx ▸ h_value
      .node left_IsBST left_le right_IsBST right_ge

  theorem insertAsInBST_infixList_Perm_cons_infixList (tree : BinaryTree type) (x : type)
  : (tree.insertAsInBST x).infixList ~ x :: tree.infixList
  :=
  open List in
  match tree with
  | nil => List.Perm.refl [x]
  | node value _ _ => 
    show infixList (ite ..) ~ _ from
    if h_value : x ≤ value then if_pos h_value ▸ 
      (insertAsInBST_infixList_Perm_cons_infixList ..).append_right _
    else if_neg h_value ▸
      ((((insertAsInBST_infixList_Perm_cons_infixList ..).cons _).trans 
        (List.Perm.swap ..).symm).append_left _).trans List.perm_middle


  def searchAsInBST (tree : BinaryTree type) (x : type) : Bool
  := match tree with
  | .nil => false
  | .node value left right =>
    if value = x then true
    else if x < value then left.searchAsInBST x
    else right.searchAsInBST x

  theorem searchAsInBST_eq_decide_Mem_of_IsBST {tree : BinaryTree type} (h_tree : tree.IsBST) 
  (x : type) : tree.searchAsInBST x = decide (x ∈ tree)
  := match tree, h_tree with
  | nil, _ => rfl
  | node value left right, 
    .node left_is_bst left_le right_is_bst right_ge => 
    show ite .. = ite .. from
    if h_e : value = x then if_pos h_e ▸ if_pos (Mem.eq h_e.symm) ▸ rfl
    else if h_l : x < value then if_neg h_e ▸ if_pos h_l ▸
      searchAsInBST_eq_decide_Mem_of_IsBST left_is_bst _ ▸
      show ite .. = _ from
      if v_in_left : x ∈ left then if_pos v_in_left ▸ if_pos v_in_left.left ▸ rfl
      else if_neg v_in_left ▸ if_neg 
      (show ¬x ∈ node value left right from
      λ | .eq h => h_e h.symm
        | .left h => v_in_left h
        | .right h => not_le_of_gt h_l $ right_ge x h
      ) ▸ rfl
    else have h_r : value < x := lt_of_le_of_ne (le_of_not_lt h_l) h_e
      if_neg h_e ▸ if_neg h_l ▸ 
      searchAsInBST_eq_decide_Mem_of_IsBST right_is_bst _ ▸
      show ite .. = _ from
      if v_in_right : x ∈ right then if_pos v_in_right ▸ if_pos v_in_right.right ▸ rfl
      else if_neg v_in_right ▸ if_neg 
      (show ¬x ∈ node value left right from
      λ | .eq h => h_e h.symm
        | .left h => not_le_of_gt h_r $ left_le x h
        | .right h => v_in_right h
      ) ▸ rfl

end

end Data.BinaryTree
