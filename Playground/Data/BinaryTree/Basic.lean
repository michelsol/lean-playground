import Std.Data.List.Lemmas

namespace Data
section
  inductive BinaryTree.{u} (type : Type u)
  | nil
  | node (value : type) (left right : BinaryTree type)
end

namespace BinaryTree
section
  def height {type} : BinaryTree type → Nat
  | nil => 0
  | node _ left right => max left.height right.height + 1

  def nodeCount {type} : BinaryTree type → Nat
  | nil => 0
  | node _ left right => left.nodeCount + right.nodeCount + 1

  def infixList {type} : BinaryTree type → List type
  | nil => []
  | node value left right => left.infixList ++ value :: right.infixList
end

section
  inductive Mem {type} : type → BinaryTree type → Prop
  | eq {value left right x} : x = value → Mem x (node value left right)
  | left {value left right x} : Mem x left → Mem x (node value left right)
  | right {value left right x} : Mem x right → Mem x (node value left right)

  instance {type} : Membership type (BinaryTree type) where
    mem := Mem
end

section
  open List

  theorem Mem.infixList_of_Mem {type} {x} {tree : BinaryTree type} (h : x ∈ tree)
    : x ∈ tree.infixList := by
    induction tree with
    | nil => contradiction
    | node value _ _ left_rec right_rec =>
      show _ ∈ _ ++ _ :: _
      rw [mem_append, mem_cons]
      cases h with
      | left h => simp [left_rec h]
      | eq h => simp [h]
      | right h => simp [right_rec h]

  theorem Mem.of_Mem_infixList {type} {x} {tree : BinaryTree type} (h : x ∈ tree.infixList)
    : x ∈ tree := by
    induction tree with
    | nil => contradiction
    | node _ _ _ left_rec right_rec =>
      have h : _ ∈ _ ++ _ :: _ := h
      rw [mem_append, mem_cons] at h
      rcases h with h | h | h
      . exact left (left_rec h)
      . exact eq h
      . exact right (right_rec h)
end

section
  theorem Mem_iff_Mem_infixList {type} (x) (tree : BinaryTree type) : x ∈ tree ↔ x ∈ tree.infixList := by
    constructor
    . exact Mem.infixList_of_Mem
    . exact Mem.of_Mem_infixList

  theorem forall_iff_forall_infixList (tree : BinaryTree type) (p : type → Prop)
    : (∀ x ∈ tree, p x) ↔ (∀ x ∈ tree.infixList, p x) := 
    ⟨λ h x => (h x) ∘ Mem.of_Mem_infixList, λ h x => (h x) ∘ Mem.infixList_of_Mem⟩

  instance decidableMem {type} [DecidableEq type] (x) (tree : BinaryTree type)
    : Decidable (x ∈ tree) :=
    match tree with
    | nil => isFalse λ.
    | node value left right => 
      let this := decidableMem x left
      let this := decidableMem x right
      if h_eq : x = value then isTrue $ Mem.eq h_eq
      else if h_left : x ∈ left then isTrue h_left.left
      else if h_right : x ∈ right then isTrue h_right.right
      else isFalse λ 
        | .eq h => h_eq h
        | .left h => h_left h
        | .right h => h_right h
end

section
  inductive LeftOrRight | left | right

  inductive IsExternalLeaf : BinaryTree type → List LeftOrRight → Prop
  | base : IsExternalLeaf .nil .nil
  | left : IsExternalLeaf tree l → IsExternalLeaf (.node value tree right) (.left :: l)
  | right : IsExternalLeaf tree l → IsExternalLeaf (.node value left tree) (.right :: l)

  def ExternalLeaf (tree : BinaryTree type) := { path : List LeftOrRight // tree.IsExternalLeaf path }

  inductive IsInternalLeaf : BinaryTree type → List LeftOrRight → Prop
  | base : IsInternalLeaf (.node value .nil .nil) .nil
  | left : IsInternalLeaf (.node value left right) l
    → IsInternalLeaf (.node new_value (.node value left right) new_right) (.left :: l)
  | right : IsInternalLeaf (.node value left right) l
    → IsInternalLeaf (.node new_value new_left (.node value left right)) (.right :: l)

  def InternalLeaf (tree : BinaryTree type) := { path : List LeftOrRight // tree.IsInternalLeaf path }

  inductive IsInternalPath : BinaryTree type → List LeftOrRight → Prop
  | base : IsInternalPath (.node value left right) .nil
  | left : IsInternalPath (.node value left right) l
    → IsInternalPath (.node new_value (.node value left right) new_right) (.left :: l)
  | right : IsInternalPath (.node value left right) l
    → IsInternalPath (.node new_value new_left (.node value left right)) (.right :: l)

  def InternalPath (tree : BinaryTree type) := { path : List LeftOrRight // tree.IsInternalPath path }

  theorem List.eq_dropLast_append_getLast (l : List α) (hl : l ≠ []) : l = l.dropLast ++ [l.getLast hl] :=
    match l with
    | [_] => rfl
    | _ :: b :: l => congrArg _ <| eq_dropLast_append_getLast (b :: l) (λ.)

  def getParent (tree : BinaryTree type) (path : InternalPath tree) (h : path.val ≠ [])
    : InternalPath tree :=
    ⟨path.val.dropLast, r tree path.val.dropLast (List.eq_dropLast_append_getLast path.val h ▸ path.property)⟩
    where r tree path {e} (isPath : tree.IsInternalPath (path ++ [e])) : tree.IsInternalPath path :=
      match tree, path, isPath with
      | .node .., [], _ => .base
      | .node _ (.node ..) _, [.left], .left _ => .left .base
      | .node _ (.node ..) _, .left :: a :: l, .left isPath =>
        .left <| r _ (a :: l) isPath
      | .node _ _ (.node ..), [.right], .right _ => .right .base
      | .node _ _ (.node ..), .right :: a :: l, .right isPath =>
        .right <| r _ (a :: l) isPath

  def InternalLeaf.toPath {tree : BinaryTree type} (path : InternalLeaf tree) : InternalPath tree :=
    ⟨path.val, r tree path.val path.property⟩
    where r tree path isPath : tree.IsInternalPath path :=
      match tree, path with
      | .node _ .nil .nil, .nil => .base
      | .node _ (.node ..) _, .left :: path => .left <| r _ path (match isPath with | .left h => h)
      | .node _ _ (.node ..), .right :: path => .right <| r _ path (match isPath with | .right h => h)

  def getTreeAt (tree : BinaryTree type) (path : InternalPath tree) : BinaryTree type :=
    r tree path.val path.property
    where r tree path isPath :=
      match tree, path with
      | .node value left right, [] => .node value left right
      | .node _ left _, .left :: path =>
        r left path (match isPath with | .left h => h)
      | .node _ _ right, .right :: path =>
        r right path (match isPath with | .right h => h)

  def insertTreeAt (tree : BinaryTree type) (path : ExternalLeaf tree) (new : BinaryTree type)
    : BinaryTree type :=
    r tree path.val path.property new
    where r tree path isPath new :=
      match tree, path with
      | .nil, [] => new
      | .node value left right, .left :: path =>
        .node value (r left path (match isPath with | .left h => h) new) right
      | .node value left right, .right :: path =>
        .node value left (r right path (match isPath with | .right h => h) new)

  def removeTreeAt (tree : BinaryTree type) (path : InternalPath tree)
    : BinaryTree type :=
    r tree path.val path.property
    where r tree path isPath :=
      match tree, path with
      | .node .., [] => .nil
      | .node value left right, .left :: path =>
        .node value (r left path (match isPath with | .left h => h)) right
      | .node value left right, .right :: path =>
        .node value left (r right path (match isPath with | .right h => h))

  def externalLeafOfRemoveTreeAt (tree : BinaryTree type) (path : InternalPath tree)
    : ExternalLeaf (tree.removeTreeAt path) :=
    ⟨path.val, r tree path.val path.property⟩
    where r tree path (isPath : IsInternalPath tree path) : (tree.removeTreeAt ⟨path, isPath⟩).IsExternalLeaf path :=
      match tree, path with
      | .node .., [] => .base
      | .node _ left _, .left :: path =>
        .left <| r left path (match isPath with | .left h => h)
      | .node _ _ right, .right :: path =>
        .right <| r right path (match isPath with | .right h => h)

  def replaceTreeAt (tree : BinaryTree type) (path : InternalPath tree) (new : BinaryTree type)
    : BinaryTree type :=
    (tree.removeTreeAt path).insertTreeAt (tree.externalLeafOfRemoveTreeAt path) new


end

end BinaryTree
end Data
