import Playground.Data.BinaryTree.BST

section
  namespace List
  variable {type} [LinearOrder type]

  def toBST (list : List type) : Data.BinaryTree.BST type
  := match list with
  | [] => .nil
  | a :: list => list.toBST.insert a

  def bstSort (list : List type) : List type := list.toBST.val.infixList

  theorem bstSort_isSorted (list : List type) : list.bstSort.IsSorted
  := (list.toBST.val.IsBST_iff_infixList_IsSorted).mp list.toBST.property

  theorem bstSort_Perm (list : List type) : list.bstSort ~ list
  := match list with
  | [] => Perm.nil
  | a :: list => 
    (list.toBST.val.insertAsInBST_infixList_Perm_cons_infixList a).trans
      (list.bstSort_Perm.cons a)

  end List
end

#eval [3, 6, 3, 2, 10, 1].bstSort
