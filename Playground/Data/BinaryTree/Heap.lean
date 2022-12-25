import Playground.Data.BinaryTree.Basic
import Mathlib.Init.Order.Defs

namespace Data.BinaryTree
section
  variable {type}
  variable [LinearOrder type]

  -- this is not a true heap without the shape property
  inductive IsHeap : BinaryTree type → Prop
  | nil : nil.IsHeap
  | node (value : type)
    (left_le : ∀ x ∈ left, x ≤ value)
    (left_IsHeap : left.IsHeap)
    (right_le : ∀ x ∈ right, x ≤ value)
    (right_IsHeap : right.IsHeap)
    : .node value left right |> IsHeap

  def heapifyDown (new_value : type)
    (left : BinaryTree type) (right : BinaryTree type) : BinaryTree type :=
    match left, right with
    | .node left_value left_left left_right, .node right_value right_left right_right => 
        let new_left := heapifyDown new_value left_left left_right
        let new_right := heapifyDown new_value right_left right_right
        if left_value ≤ new_value then
          if right_value ≤ new_value then .node new_value left right
          else .node right_value left new_right
        else .node left_value new_left right
    | .node left_value left_left left_right, .nil =>
      let new_left := heapifyDown new_value left_left left_right
      if left_value ≤ new_value then .node new_value left .nil
      else .node left_value new_left .nil
    | .nil, .node right_value right_left right_right =>
      let new_right := heapifyDown new_value right_left right_right
      if right_value ≤ new_value then .node new_value .nil right
      else .node right_value .nil new_right
    | .nil, .nil => .node new_value .nil .nil
  termination_by _ new_value left right => left.nodeCount + right.nodeCount
  decreasing_by
    simp_wf
    dsimp [nodeCount]
    simp_arith

  def heapifyDown_IsHeap_of_IsHeap
    (new_value : type)
    (left right : BinaryTree type)
    (left_IsHeap : left.IsHeap)
    (right_IsHeap : right.IsHeap)
    : (heapifyDown new_value left right).IsHeap :=
    match left, right, left_IsHeap, right_IsHeap with
    | .node left_value left_left left_right
    , .node right_value right_left right_right
    , .node _ left_left_le left_left_IsHeap left_right_le left_right_IsHeap
    , .node _ right_left_le right_left_IsHeap right_right_le right_right_IsHeap =>
      let left := node left_value left_left left_right
      let right := node right_value right_left right_right
      have left_IsHeap : left.IsHeap := .node _ left_left_le left_left_IsHeap left_right_le left_right_IsHeap
      have right_IsHeap : right.IsHeap := .node _ right_left_le right_left_IsHeap right_right_le right_right_IsHeap
      let new_left := heapifyDown new_value left_left left_right
      have new_left_IsHeap : new_left.IsHeap := sorry --heapifyDown_IsHeap_of_IsHeap _ _ _ left_left_IsHeap left_right_IsHeap
      let new_right := heapifyDown new_value right_left right_right
      have new_right_IsHeap : new_right.IsHeap := sorry --heapifyDown_IsHeap_of_IsHeap _ _ _ right_left_IsHeap right_right_IsHeap
      if hleft : left_value ≤ new_value then
        if hright : right_value ≤ new_value then
          show IsHeap (ite _ (ite ..) _) from if_pos hleft ▸ if_pos hright ▸ 
          show IsHeap (.node new_value left right) from
          .node
            new_value
            (λ x => λ (hx : _ ∈ node ..) => match hx with
              | .eq hx => hx ▸ hleft
              | .left hx => le_trans (left_left_le x hx) hleft
              | .right hx => le_trans (left_right_le x hx) hleft)
            left_IsHeap
            (λ x => λ (hx : _ ∈ node ..) => match hx with
              | .eq hx => hx ▸ hright
              | .left hx => le_trans (right_left_le x hx) hright
              | .right hx => le_trans (right_right_le x hx) hright)
            right_IsHeap
        else
          show IsHeap (ite _ (ite ..) _) from if_pos hleft ▸ if_neg hright ▸ 
          show IsHeap (.node right_value left new_right) from
          have hlr : left_value ≤ right_value := le_trans hleft $ le_of_lt $ lt_of_not_ge hright
          .node
            right_value
            (λ x => λ (hx : _ ∈ node ..) => match hx with
              | .eq hx => hx ▸ hlr
              | .left hx => le_trans (left_left_le x hx) hlr
              | .right hx => le_trans (left_right_le x hx) hlr)
            left_IsHeap
            (λ x => λ (hx : _ ∈ _) =>
              sorry)
            new_right_IsHeap
      else
        show IsHeap (ite _ (ite ..) _) from if_neg hleft ▸
        show IsHeap (.node left_value new_left right) from
          .node
            left_value 
            (λ x => λ (hx : _ ∈ _) =>
              sorry)
            new_left_IsHeap
            (λ x => λ (hx : _ ∈ _) =>
              sorry)
            right_IsHeap
    | _, _, _, _ =>
      sorry


  -- def heapifyUp (new_value : type)
  --   (subtree : BinaryTree type)  : BinaryTree type :=

end
end Data.BinaryTree