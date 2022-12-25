import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

abbrev DecidableSet.{u} {α : Type u} (r : Set α) := (a : α) → Decidable (a ∈ r)
instance {α} (s : Set α) [DecidableSet s] : DecidableSet s.compl := λ _ => show Decidable (¬_) from inferInstance
instance {α} [DecidableEq α] (j : α) : DecidableSet {j} := λ _ => show Decidable (_ = _) from inferInstance

structure SimpleGraph (α) [Fintype α] [DecidableEq α] where
  isEdge : α → α → Prop
  decidable_isEdge : ∀ i j, Decidable (isEdge i j)

section
  variable {α} [Fintype α] [DecidableEq α]

  namespace SimpleGraph
  section
    variable (graph : SimpleGraph α)

    instance : ∀ i j, Decidable (graph.isEdge i j) := graph.decidable_isEdge

    instance : ∀ i, DecidableSet (graph.isEdge i) := graph.decidable_isEdge

    abbrev nodesOutOf (i : α) : Set α := (graph.isEdge i .)

    abbrev nodesInto (j : α) : Set α := (graph.isEdge . j)

    def induce (s : Set α) [DecidableSet s] : SimpleGraph { x : α // x ∈ s } where
      isEdge | ⟨i, _⟩, ⟨j, _⟩ => graph.isEdge i j
      decidable_isEdge | ⟨i, _⟩, ⟨j, _⟩ => graph.decidable_isEdge i j

    def original {s : Set α} [DecidableSet s] (g : SimpleGraph { x : α // x ∈ s }) : SimpleGraph α where
      isEdge i j := if h : i ∈ s ∧ j ∈ s then g.isEdge ⟨i, h.1⟩ ⟨j, h.2⟩ else False
      decidable_isEdge := inferInstance
    
    def SubsetSet (s : Set α) [DecidableSet s] := ∀ i j, graph.isEdge i j → i ∈ s ∧ j ∈ s


  end

  end SimpleGraph
end

example (α : Type) [Fintype α] (s : Set α) : Finset α := 
--  s.fio
sorry

example (α : Type) [DecidableEq α] (h : Fintype α) (s : Set α) : Fintype s := 
⟨
  let x := h.elems.image λ t => t
  sorry, sorry⟩
