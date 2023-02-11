import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

abbrev DecidableSet.{u} {α : Type u} (r : Set α) := (a : α) → Decidable (a ∈ r)
instance {α} (s : Set α) [DecidableSet s] : DecidableSet s.compl := λ _ => show Decidable (¬_) from inferInstance
instance {α} [DecidableEq α] (j : α) : DecidableSet {j} := λ _ => show Decidable (_ = _) from inferInstance


noncomputable
def Set.size {α} [i : Fintype α] [DecidableEq α] (s : Set α) [DecidableSet s] : Nat :=
  (i.elems.filter (decide $ . ∈ s)).toList.length

structure SimpleGraph (α) [Fintype α] [DecidableEq α] where
  isEdge : α → α → Bool

section
  variable {α} [Fintype α] [DecidableEq α]
  -- instance : ∀ i j, Decidable (graph.isEdge i j) := graph.decidable_isEdge
  -- instance : ∀ i, DecidableSet (graph.isEdge i) := graph.decidable_isEdge

  namespace SimpleGraph
  section
    variable (graph : SimpleGraph α)
    abbrev nodesOutOf (i : α) : Set α := (graph.isEdge i . = true)
    abbrev nodesInto (j : α) : Set α := (graph.isEdge . j = true)
    -- def degreeOutOf (i) := (graph.nodesOutOf i).size
    -- def degreeInto (i) := (graph.nodesInto i).size
    -- def IsLeaf (i) := graph.degreeOutOf i = 1

    def induce (s : Set α) [DecidableSet s] : SimpleGraph { x : α // x ∈ s } where
      isEdge | ⟨i, _⟩, ⟨j, _⟩ => graph.isEdge i j 
  end

  variable (graph : SimpleGraph α) in
  inductive Walk : α → α → Type where
  | nil (i) : Walk i i -- path with 0 moves from i to i. Not a path with 1 move along edge i->i
  | cons (i k) (w : Walk i k) (j) (h : graph.isEdge k j = true) : Walk i j

  def WalkIn (graph : SimpleGraph α) (s : Set α) [DecidableSet s] (i j : { x : α // x ∈ s }) :=
    (graph.induce s).Walk i j
  def WalkNotIn (graph : SimpleGraph α) (s : Set α) [DecidableSet s] := graph.WalkIn s.compl

  section
    variable {graph : SimpleGraph α}
    namespace Walk
    def length {i j} : graph.Walk i j → Nat
      | nil i => 0
      | cons i k w j h => w.length + 1

    def nodeList {i j} : graph.Walk i j → List α
      | nil i => [i]
      | cons i k w j h => j :: w.nodeList

    def nodes {i j} : graph.Walk i j → Set α
      | nil i => {i}
      | cons i k w j h => w.nodes ∪ {j}
    
    theorem first_mem_nodeList {i j} (w : graph.Walk i j) : i ∈ w.nodeList :=
      match w with
      | nil _ => List.Mem.head []
      | cons _ _ w _ _ => List.Mem.tail _ w.first_mem_nodeList
    theorem last_mem_nodeList {i j} (w : graph.Walk i j) : j ∈ w.nodeList :=
      match w with
      | nil _ => List.Mem.head []
      | cons _ _ _ _ _ => List.Mem.head _
    def WalkNotIn_of_notIn_nodeList {i j} (w : graph.Walk i j) {a} (h : a ∉ w.nodeList) :=
      graph.WalkNotIn {a}
        ⟨i, λ c => by subst c; exact h w.first_mem_nodeList⟩
        ⟨j, λ c => by subst c; exact h w.last_mem_nodeList⟩
    def to_WalkNotIn_of_notIn_nodeList {i j} (w : graph.Walk i j) {a} (h : a ∉ w.nodeList)
      : w.WalkNotIn_of_notIn_nodeList h :=
      match w, h with
      | Walk.nil _, h => Walk.nil _
      | Walk.cons _ k w _ hks, h =>
        let r := (to_WalkNotIn_of_notIn_nodeList w λ c => h $ List.mem_cons.mpr $ Or.inr c)
        Walk.cons _ _ r _ hks
    theorem to_WalkNotIn_of_notIn_nodeList_preserves_nodeList {i j} (w : graph.Walk i j) {a} (h : a ∉ w.nodeList)
      : (w.to_WalkNotIn_of_notIn_nodeList h).nodeList.map Subtype.val = w.nodeList := 
      match w, h with
      | Walk.nil _, h => rfl
      | Walk.cons i k w j hks, h => 
        congrArg (List.cons j) $ 
        to_WalkNotIn_of_notIn_nodeList_preserves_nodeList w λ c => h $ List.mem_cons.mpr $ Or.inr c

    theorem first_mem_nodes {i j} (w : graph.Walk i j) : i ∈ w.nodes :=
      match w with
      | nil _ => rfl
      | cons _ k w _ h => Or.inl w.first_mem_nodes
    theorem last_mem_nodes {i j} (w : graph.Walk i j) : j ∈ w.nodes :=
      match w with
      | nil _ => rfl
      | cons _ k w _ h => Or.inr rfl
    def to_WalkIn_of_Subset {i j} (w : graph.Walk i j) {s} [DecidableSet s] (h : w.nodes ⊆ s)
      : graph.WalkIn s ⟨i, h w.first_mem_nodes⟩ ⟨j, h w.last_mem_nodes⟩ :=
      match w, h with
      | Walk.nil _, h => Walk.nil _
      | Walk.cons _ k w _ hks, h =>
        let r := w.to_WalkIn_of_Subset λ _ hx => h (Or.inl hx)
        Walk.cons _ _ r _ hks
    theorem to_WalkIn_of_Subset_preserves {i j} (w : graph.Walk i j) {s} [DecidableSet s] (h : w.nodes ⊆ s)
      : (w.to_WalkIn_of_Subset h).nodes = sorry := sorry


    end Walk

  end


  def Path (graph : SimpleGraph α) (i j) := { w : graph.Walk i j // List.Nodup w.nodeList }

  def Path2 (graph : SimpleGraph α) (i j) := { w : graph.Walk i j // ∀ i, i ∈ w.nodes → False }
  #exit

  section
    variable {graph : SimpleGraph α}
    namespace Path
    def cons  {i k : α} (p : graph.Path i k) {j : α} (h : graph.isEdge k j = true) (hj : j ∉ p.val.nodeList)
      : graph.Path i j :=
      ⟨Walk.cons _ _ p.val _ h, List.nodup_cons.mpr ⟨hj, p.property⟩⟩

    def to_PathNotIn_of_notIn_nodeList {i j} (p : graph.Path i j) {a} (h : a ∉ p.val.nodeList)
      : (graph.induce (Set.compl {a})).Path
          ⟨i, λ c => by subst c; exact h p.val.first_mem_nodeList⟩
          ⟨j, λ c => by subst c; exact h p.val.last_mem_nodeList⟩ :=
      match i, j, p, h with
      | _, _, ⟨Walk.nil _, _⟩, h => ⟨Walk.nil _, List.nodup_singleton _⟩
      | i, j, ⟨Walk.cons _ k w _ hks, hn⟩, h =>
        have hn := List.nodup_cons.mp hn
        let wr : Walk .. := (w.to_WalkNotIn_of_notIn_nodeList λ c => h $ List.mem_cons.mpr $ Or.inr c)
        have hr : wr.nodeList.map _ = w.nodeList := w.to_WalkNotIn_of_notIn_nodeList_preserves_nodeList _
        have : List.Nodup wr.nodeList := sorry -- from hn, via hr using the fact that map is injective
        let r : Path .. := ⟨wr, this⟩
        r.cons hks $ show _ ∉ wr.nodeList from sorry -- from hn using hr

    def to_PathIn_of_Subset {i j} (p : graph.Path i j) {s} [DecidableSet s] (h : p.val.nodes ⊆ s)
      : (graph.induce s).Path ⟨i, h p.val.first_mem_nodes⟩ ⟨j, h p.val.last_mem_nodes⟩ :=
      match i, j, p, h with
      | _, _, ⟨Walk.nil _, _⟩, h => ⟨Walk.nil _, List.nodup_singleton _⟩
      | i, j, ⟨Walk.cons _ k w _ hks, hn⟩, h =>
      sorry

#exit

    end Path
  end
  
  example (a : List α) (b : List β) (f : α → β) (hf : f.Injective) (h : a.map f = b) (ha : a.Nodup) : b.Nodup :=
    sorry

  #exit

  section
    variable (graph : SimpleGraph α)

    def Connected := ∀ i j, Nonempty (graph.Walk i j)
    def Cycle (i) := { w : graph.Walk i i // w.length ≠ 0 }
    def Acyclic := ∀ i, graph.Cycle i → False

    theorem exists_nil_Walk_iff (i j) : (∃ w : graph.Walk i j, w.length = 0) ↔ i = j :=
      ⟨λ ⟨w, _⟩ => match w with | Walk.nil i => rfl, λ h => h ▸ ⟨Walk.nil i, rfl⟩⟩

    theorem exists_Walk_iff (i j) (m)
      : (∃ w : graph.Walk i j, w.length = m + 1) ↔ ∃ k, (∃ w : graph.Walk i k, w.length = m) ∧ graph.isEdge k j :=
    ⟨λ ⟨Walk.cons i k w _ hkj, hw⟩ => ⟨k, ⟨⟨w, Nat.succ.inj hw⟩, hkj⟩⟩
    , λ ⟨k, ⟨⟨w, hw⟩, hkj⟩⟩ => ⟨Walk.cons i k w j hkj, congrArg (. + 1) hw⟩⟩

    def decidable_exists_nonnil_Walk (i j) (m : Nat) : Decidable (∃ w : graph.Walk i j, w.length = m + 1) := by
        rw [graph.exists_Walk_iff i j m]
        suffices ∀ k, Decidable ((∃ w : graph.Walk i k, w.length = m) ∧ graph.isEdge k j) from Fintype.decidableExistsFintype
        intro k
        match m with
        | 0 => rw [graph.exists_nil_Walk_iff]; infer_instance
        | m + 1 => let _ := decidable_exists_nonnil_Walk i k m; infer_instance

    def decidable_exists_Walk (i j) (m : Nat) : Decidable (∃ w : graph.Walk i j, w.length = m) := match m with
      | 0 => by rw [graph.exists_nil_Walk_iff i j]; infer_instance
      | m  + 1 => graph.decidable_exists_nonnil_Walk i j m

    -- use the fact that graph is finite so there must be a finite length walk that explores all possibilities
    def decidable_Nonempty_Walk (i j) : Decidable $ Nonempty (graph.Walk i j) :=
        sorry
    

    -- theorem exists_nil_Path_iff (i j) : (∃ w : graph.Walk i j, w.length = 0) ↔ i = j :=
    --   ⟨λ ⟨w, _⟩ => match w with | Walk.nil i => rfl, λ h => h ▸ ⟨Walk.nil i, rfl⟩⟩

    theorem exists_Path_iff (i j) (m)
      : (∃ w : graph.Path i j, w.val.length = m + 1) ↔ ∃ k, (∃ w : graph.Path i k, j ∉ w.val.nodeList ∧ w.val.length = m) ∧ graph.isEdge k j :=
    ⟨λ ⟨⟨Walk.cons i k w _ hkj, pw⟩, hw⟩ => 
      have pw := List.nodup_cons.mp pw
      ⟨k, ⟨⟨⟨w, pw.2⟩, ⟨pw.1, Nat.succ.inj hw⟩⟩, hkj⟩⟩
    , λ ⟨k, ⟨⟨w, ⟨pw, hw⟩⟩, hkj⟩⟩ =>
      have pw := List.nodup_cons.mpr ⟨pw, w.prop⟩
      ⟨⟨Walk.cons i k w.val j hkj, pw⟩, congrArg (. + 1) hw⟩⟩

    theorem exists_Path_iff2 (i j) (m)
      : (∃ w : graph.Path i j, w.val.length = m + 1) ↔ ∃ k, (∃ w : (graph.cutNodes {j}).Path ⟨i, sorry⟩ ⟨k, sorry⟩, w.val.length = m) ∧ graph.isEdge k j :=
    ⟨λ ⟨⟨Walk.cons i k w _ hkj, pw⟩, hw⟩ => 
      have pw := List.nodup_cons.mp pw
      ⟨k, ⟨⟨⟨sorry, sorry⟩, sorry⟩, hkj⟩⟩,
    sorry⟩



    def decidable_exists_nonnil_Path {α} [Fintype α] [DecidableEq α] (graph : SimpleGraph α)
      (i j) (m : Nat) : Decidable (∃ w : graph.Path i j, w.val.length = m + 1) := by
        rw [graph.exists_Path_iff i j m]
        suffices ∀ k, Decidable ((∃ w : graph.Path i k, j ∉ w.val.nodeList ∧ w.val.length = m) ∧ graph.isEdge k j) from Fintype.decidableExistsFintype
        intro k
        match m with
        | 0 => sorry
        | m + 1 => 
          let g := graph.cutNodes {j} 
          let inst := decidable_exists_nonnil_Path g ⟨i, sorry⟩ ⟨k, sorry⟩ m
          -- infer_instance
          sorry



    -- theorem degreeInto_ge_1_of_Connected_and_ge_2 (hn : n ≥ 2) (hc : graph.Connected) (i : Fin n)
    --   : graph.degreeInto i ≥ 1 :=
    --   let j : Fin n := if i = ⟨0, by linarith⟩ then ⟨1, by linarith⟩ else ⟨0, by linarith⟩
    --   have : i.1 ≠ j.1 := sorry
    --   match (hc j i).some with
    --   | .cons _ k w i h => sorry

    -- def findLeaf (hn : n ≥ 2) (hc : graph.Connected) (ha : graph.Acyclic) : Fin n :=
    --   match n, hn with
    --   | 2, _ => 0
    --   | n + 1, _ =>
    --     sorry
  end
  end SimpleGraph
end