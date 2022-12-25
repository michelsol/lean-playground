import Playground.Data.SimpleGraph.Basic

section
  variable {α} [Fintype α] [DecidableEq α]

  namespace SimpleGraph

  variable (graph : SimpleGraph α) in
  inductive Walk : α → α → Type where
  | nil (i) : Walk i i -- path with 0 moves from i to i. Not a path with 1 move along edge i->i
  | cons (i k) (w : Walk i k) (j) (h : graph.isEdge k j) : Walk i j

  section
    variable {graph : SimpleGraph α}
    
    namespace Walk

    def length {i j} : graph.Walk i j → Nat
      | nil i => 0
      | cons _ _ w _ h => w.length + 1

    def nodeList {i j} : graph.Walk i j → List α
      | nil i => [i]
      | cons _ _ w _ h => j :: w.nodeList

    theorem nodeList_length_eq {i j} (w : graph.Walk i j) : w.nodeList.length = w.length + 1 := by
      induction w with
      | nil => rfl
      | cons _ w _ _ ih => exact congrArg (. + 1) ih

    theorem first_mem_nodeList {i j} (w : graph.Walk i j) : i ∈ w.nodeList := by
      induction w with
      | nil =>
        show i ∈ _ :: _
        exact List.mem_singleton.mpr rfl
      | cons k w j _ ih => 
        show i ∈ _ :: _
        exact List.mem_cons_of_mem j ih

    theorem last_mem_nodeList {i j} (w : graph.Walk i j) : j ∈ w.nodeList := by
      cases w with
      | nil =>
        show i ∈ _ :: _
        exact List.mem_singleton.mpr rfl
      | cons k w j h =>
        show j ∈ _ :: _
        exact List.mem_cons_self j _


    def nodes {i j} : graph.Walk i j → Set α
      | nil i => {i}
      | cons i _ w j h => w.nodes ∪ {j}

    theorem first_mem_nodes {i j} (w : graph.Walk i j) : i ∈ w.nodes := by
      induction w with
      | nil => rfl
      | cons k w j _ ih => 
        show i ∈ _ ∪ _
        left
        exact ih

    theorem last_mem_nodes {i j} (w : graph.Walk i j) : j ∈ w.nodes := by
      cases w with
      | nil => rfl
      | cons k w j h =>
        show j ∈ _ ∪ _
        right
        rfl



    theorem nodeList_Mem_iff {i j} (w : graph.Walk i j)
      : ∀ x, (x ∈ w.nodeList) ↔ (x ∈ w.nodes) := by
      intro x
      induction w with
      | nil =>  
        show x ∈ [i] ↔ x ∈ ({i} : Set _)
        rw [List.mem_singleton, Set.mem_singleton_iff]
      | cons k w j _ w_ih =>
        have w_ih : x ∈ w.nodeList ↔ x ∈ w.nodes := w_ih
        show (x ∈ _ :: _) ↔ (x ∈ ((_ ∪ _) : Set _))
        rw [Set.mem_union, Set.mem_singleton_iff]
        rw [List.mem_cons]
        rw [w_ih]
        exact or_comm

    private def original_impl {s} [DecidableSet s] {i j} {hi hj} 
      (w : (graph.induce s).Walk ⟨i, hi⟩ ⟨j, hj⟩)
      : graph.Walk i j :=
      match w with
      | Walk.nil _ => Walk.nil i
      | Walk.cons _ ⟨k, _⟩ w _ h => Walk.cons i k w.original_impl j h

    @[implemented_by original_impl]
    def original {s} [DecidableSet s] {i j} {hi hj} 
      (w : (graph.induce s).Walk ⟨i, hi⟩ ⟨j, hj⟩)
      : graph.Walk i j := by
        apply w.recOn (motive := λ ⟨j, _⟩ _ => graph.Walk i j)
        . exact Walk.nil i
        . intro ⟨k, hk⟩ _ ⟨j, hj⟩ hkj wk
          exact wk.cons i k j hkj


    theorem original_nodes_eq {s} [DecidableSet s] {i j} {hi hj}
      (w : (graph.induce s).Walk ⟨i, hi⟩ ⟨j, hj⟩)
      : w.original.nodes = (↑) '' w.nodes := by
      match w with
      | Walk.nil _ => 
        show {_} = Subtype.val '' {_}
        rw [Set.image_singleton]
      | Walk.cons _ _ w _ _ =>
        show w.original.nodes ∪ {_} = Subtype.val '' (w.nodes ∪ {_})
        rw [Set.image_union, Set.image_singleton]
        congr
        exact w.original_nodes_eq

  theorem original_nodes_subset {s} [DecidableSet s] {i j} {hi hj}
      (w : (graph.induce s).Walk ⟨i, hi⟩ ⟨j, hj⟩)
      : w.original.nodes ⊆ s := by
      rw [original_nodes_eq]
      intro x ⟨z, hz⟩
      rw [←hz.2]
      exact z.2

    theorem original_nodeList_eq {s} [DecidableSet s] {i j} {hi hj}
      (w : (graph.induce s).Walk ⟨i, hi⟩ ⟨j, hj⟩)
      : w.original.nodeList = w.nodeList.map (↑) := by
      match w with
      | Walk.nil _ => rfl
      | Walk.cons _ _ w _ _ =>
        apply congrArg (List.cons j)
        exact w.original_nodeList_eq

    theorem original_Nodup_of_Nodup {s} [DecidableSet s] {i j} {hi hj} 
      (w : (graph.induce s).Walk ⟨i, hi⟩ ⟨j, hj⟩)
      (hw : w.nodeList.Nodup) : w.original.nodeList.Nodup := by
        rw [original_nodeList_eq]
        exact (List.nodup_map_iff Subtype.val_injective).2 hw


    def induce {s} [DecidableSet s] {i j} (w : graph.Walk i j) (h : w.nodes ⊆ s)
      : (graph.induce s).Walk ⟨i, h w.first_mem_nodes⟩ ⟨j, h w.last_mem_nodes⟩ :=
      match w, h with
      | Walk.nil _, _ => Walk.nil _
      | Walk.cons _ _ w _ hkj, h =>
        let r := w.induce $ (w.nodes.subset_union_left {j}).trans h
        r.cons _ _ _ hkj

    theorem induce_nodeList_map_eq {s} [DecidableSet s] {i j}
      (w : graph.Walk i j) (h : w.nodes ⊆ s)
      : (w.induce h).nodeList.map (↑) = w.nodeList := by
      induction w with
      | nil => rfl
      | cons k w j hkj w_ih =>
        show j :: _ = j :: _
        apply congrArg (List.cons j)
        exact w_ih _

    theorem induce_Nodup_of_Nodup {s} [DecidableSet s] {i j}
      (w : graph.Walk i j) (h : w.nodes ⊆ s) (hw : w.nodeList.Nodup)
      : (w.induce h).nodeList.Nodup := by
          apply (List.nodup_map_iff Subtype.val_injective).1
          rw [induce_nodeList_map_eq]
          exact hw

    end Walk

  end

  end SimpleGraph
end