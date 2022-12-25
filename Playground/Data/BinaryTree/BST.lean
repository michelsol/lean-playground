import Playground.Data.BinaryTree.IsBST

namespace Data.BinaryTree
section
  def BST (type : Type u) [LinearOrder type] := { tree : BinaryTree type // tree.IsBST }
end

namespace BST
section
  variable {type} [LinearOrder type]

  instance : Coe (BST type) (BinaryTree type) := ⟨Subtype.val⟩

  def nil : BST type := ⟨.nil, .nil⟩

  def insert (tree : BST type) (value : type) : BST type
  := ⟨tree.val.insertAsInBST value, insertAsInBST_IsBST_of_IsBST tree.property value⟩

  def search (tree : BST type) (value : type) : Bool
  := tree.val.searchAsInBST value

end
end BST
end Data.BinaryTree