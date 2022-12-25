import Playground.Data.SimpleGraph.Walk
import Mathlib.Data.Fintype.Card

section
  variable {α} [Fintype α] [DecidableEq α]
  namespace SimpleGraph

  def Path (graph : SimpleGraph α) (i j) := { w : graph.Walk i j // w.nodeList.Nodup }

  section
    variable {graph : SimpleGraph α}
    namespace Path

    def cons  {i k : α} (p : graph.Path i k) {j : α} (h : graph.isEdge k j) (hj : j ∉ p.val.nodeList)
      : graph.Path i j :=
      ⟨Walk.cons _ _ p.val _ h, List.nodup_cons.mpr ⟨hj, p.property⟩⟩

    def toWalk {i j} (p : graph.Path i j) : graph.Walk i j := p.1

    def toWalkNodup {i j} (p : graph.Path i j) : p.toWalk.nodeList.Nodup := p.2

    def original {s} [DecidableSet s] {i j} {hi hj} 
      (p : (graph.induce s).Path ⟨i, hi⟩ ⟨j, hj⟩) : graph.Path i j := 
        ⟨p.toWalk.original, p.toWalk.original_Nodup_of_Nodup p.toWalkNodup⟩

    def induce {s} [DecidableSet s] {i j} (p : graph.Path i j) (h : p.toWalk.nodes ⊆ s)
      : (graph.induce s).Path ⟨i, h p.toWalk.first_mem_nodes⟩ ⟨j, h p.toWalk.last_mem_nodes⟩ :=
      ⟨p.toWalk.induce h, p.toWalk.induce_Nodup_of_Nodup h p.toWalkNodup⟩

    theorem length_lt_card {i j} (p : graph.Path i j) : p.toWalk.length < Fintype.card α := by
      show _ + 1 ≤ _
      rw [←p.toWalk.nodeList_length_eq]
      exact p.property.length_le_card

    end Path
    namespace Walk

    -- follow nodes, drop cycles along the way by ignoring previously met nodes, stop when j is first met
    def extractPathWalk {i j} (w : graph.Walk i j) : graph.Walk i j :=
      let first_j_idx := w.nodeList.findIdx (. = j) -- TODO change this with proof-friendly function (non tail rec)
      sorry

    theorem extractPathWalkNodup {i j} (w : graph.Walk i j) : w.extractPathWalk.nodeList.Nodup := by
      sorry

    def extractPath {i j} (w : graph.Walk i j) : graph.Path i j := ⟨w.extractPathWalk, w.extractPathWalkNodup⟩

    end Walk
  end
  
  end SimpleGraph
end