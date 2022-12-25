import Playground.Data.SimpleGraph.Path

section
  variable {α} [Fintype α] [DecidableEq α]
  namespace SimpleGraph

  section
    variable (graph : SimpleGraph α)

    def Connected := ∀ i j, Nonempty (graph.Walk i j)

    theorem exists_nil_Walk_iff (i j) : (∃ w : graph.Walk i j, w.length = 0) ↔ i = j := by
      constructor
      . intro ⟨w, _⟩
        cases w with
        | nil  => rfl
        | cons => contradiction
      . intro h
        subst h
        use Walk.nil i
        rfl

    theorem exists_nonnil_Walk_iff (i j) (m) :
      (∃ w : graph.Walk i j, w.length = m + 1) ↔ ∃ k, (∃ w : graph.Walk i k, w.length = m) ∧ graph.isEdge k j := by
      constructor
      . intro ⟨Walk.cons i k w _ hkj, hw⟩
        use k
        constructor
        . use w
          exact Nat.succ.inj hw
        . exact hkj
      . intro ⟨k, ⟨⟨w, hw⟩, hkj⟩⟩
        use Walk.cons i k w j hkj
        exact congrArg (. + 1) hw

    def decidable_exists_nonnil_Walk (i j) (m : Nat) : Decidable (∃ w : graph.Walk i j, w.length = m + 1) := by
        rw [graph.exists_nonnil_Walk_iff i j m]
        suffices ∀ k, Decidable ((∃ w : graph.Walk i k, w.length = m) ∧ graph.isEdge k j) from Fintype.decidableExistsFintype
        intro k
        match m with
        | 0 => rw [graph.exists_nil_Walk_iff]; infer_instance
        | m + 1 => let _ := decidable_exists_nonnil_Walk i k m; infer_instance

    def decidable_exists_Walk (i j) (m : Nat) : Decidable (∃ w : graph.Walk i j, w.length = m) := match m with
      | 0 => by rw [graph.exists_nil_Walk_iff i j]; infer_instance
      | m  + 1 => graph.decidable_exists_nonnil_Walk i j m

    -- use the fact that graph is finite so there must be a finite length PATH that explores all possibilities
    -- def decidable_Nonempty_Walk (i j) : Decidable $ Nonempty (graph.Walk i j) := sorry

    theorem exists_nil_Path_iff (i j) : (∃ p : graph.Path i j, p.toWalk.length = 0) ↔ i = j := by
      constructor
      . intro ⟨p, _⟩
        let ⟨w, hw⟩ := p
        cases w with
        | nil  => rfl
        | cons => contradiction
      . intro h
        subst h
        use ⟨Walk.nil i, ?_⟩
        . show (Walk.nil i).length = 0; rfl
        show List.Nodup [i]
        exact List.nodup_singleton i

    theorem exists_nonnil_Path_iff (i j) (m) :
      (∃ p : graph.Path i j, p.toWalk.length = m + 1) ↔ ∃ k, (∃ p : graph.Path i k, j ∉ p.toWalk.nodeList ∧ p.toWalk.length = m) ∧ graph.isEdge k j := by
      constructor
      . intro ⟨⟨Walk.cons i k w _ hkj, hp⟩, hl⟩
        have hp := List.nodup_cons.mp hp
        use k
        constructor
        . use ⟨w, hp.2⟩
          constructor
          . exact hp.1
          . exact Nat.succ.inj hl
        . exact hkj
      . intro ⟨k, ⟨⟨w, ⟨hp, hl⟩⟩, hkj⟩⟩
        have hp := List.nodup_cons.mpr ⟨hp, w.prop⟩
        use ⟨Walk.cons i k w.val j hkj, hp⟩
        exact congrArg (. + 1) hl

    def decidable_exists_nonnil_Path {α} [Fintype α] [DecidableEq α] (graph : SimpleGraph α)
      (i j) (m : Nat) : Decidable (∃ p : graph.Path i j, p.toWalk.length = m + 1) := by
        rw [graph.exists_nonnil_Path_iff i j m]
        suffices ∀ k, Decidable ((∃ p : graph.Path i k, j ∉ p.toWalk.nodeList ∧ p.toWalk.length = m) ∧ graph.isEdge k j) from Fintype.decidableExistsFintype
        intro k
        suffices Decidable (∃ p : graph.Path i k, j ∉ p.toWalk.nodeList ∧ p.toWalk.length = m) from inferInstance
        by_cases hi : i = j
        . apply isFalse
          subst hi
          intro ⟨p, h, _⟩
          exact h p.toWalk.first_mem_nodeList
        by_cases hk : k = j
        . apply isFalse
          subst hk
          intro ⟨p, h, _⟩
          exact h p.toWalk.last_mem_nodeList
        . match m with
          | 0 =>
            by_cases hik : i = k
            . apply isTrue
              subst hik
              use ⟨Walk.nil _, List.nodup_singleton _⟩
              constructor
              . show _ ∉ [_]
                rw [List.mem_singleton]
                intro c
                exact hi c.symm
              . rfl
            . apply isFalse
              intro ⟨⟨w, _⟩, _, (hw : w.length = 0)⟩
              cases w <;> contradiction
          | m + 1 =>
            let g := graph.induce {j}ᶜ
            let inst := decidable_exists_nonnil_Path g ⟨i, hi⟩ ⟨k, hk⟩ m
            let prop := ∃ p : g.Path ⟨i, hi⟩ ⟨k, hk⟩, p.toWalk.length = m + 1
            apply decidable_of_iff prop
            show (∃ p, _) ↔ (∃ p, _)
            constructor
            . intro ⟨p, hp⟩
              use p.original
              constructor
              . have := p.toWalk.original_nodes_subset
                rw [Set.subset_compl_singleton_iff] at this
                show ¬ j ∈ p.toWalk.original.nodeList
                rw [p.toWalk.original.nodeList_Mem_iff j]
                exact this
              . let w := p.toWalk
                have hp : w.length = _ := hp
                show w.original.length = _
                suffices w.original.length = w.length from this ▸ hp
                apply w.recOn (motive := λ _ w' => w'.original.length = w'.length) -- induction w
                . rfl
                . intro _ w _ _ ih
                  show w.original.length + 1 = w.length + 1
                  exact congrArg (. + 1) ih
            . intro ⟨p, hpj, hpm⟩
              exact ⟨p.induce $ by
                rw [Set.subset_compl_singleton_iff]
                rw [←p.toWalk.nodeList_Mem_iff j]
                exact hpj
              , by
                let w := p.toWalk
                show (w.induce _).length = _
                suffices (w.induce _).length = w.length from this ▸ hpm
                rw [p.toWalk.nodeList_Mem_iff j] at hpj
                have hpj : w.nodes ⊆ _ := Set.subset_compl_singleton_iff.mpr hpj
                revert hpj
                apply w.recOn (motive := λ _ w' => (h' : w'.nodes ⊆ {j}ᶜ) → (w'.induce h').length = w'.length)
                . intro _ ; rfl
                . intro _ w' _ _ ih _
                  show (w'.induce _).length + 1 = w'.length + 1
                  exact congrArg (. + 1) $ ih _
              ⟩

    def decidable_exists_Path_with_length (i j) (m : Nat) : Decidable (∃ p : graph.Path i j, p.toWalk.length = m) := match m with
      | 0 => by rw [graph.exists_nil_Path_iff i j]; infer_instance
      | m  + 1 => graph.decidable_exists_nonnil_Path i j m

    def decidable_exists_Path (i j) : Decidable $ Nonempty (graph.Path i j) :=
      let prop := ∃ m : Fin (Fintype.card α), ∃ p : graph.Path i j, p.toWalk.length = m
      suffices Decidable prop from decidable_of_iff prop $ by
        constructor
        . intro ⟨_, p, _⟩
          exact ⟨p⟩
        . intro ⟨p⟩
          use ⟨p.toWalk.length, p.length_lt_card⟩
          use p
      suffices ∀ m : Fin (Fintype.card α), Decidable $ ∃ p : graph.Path i j, p.toWalk.length = m from Fintype.decidableExistsFintype
      λ _ => graph.decidable_exists_Path_with_length i j _

    -- theorem degreeInto_ge_1_of_Connected (h : Fintype.card α ≥ 2) (hc : graph.Connected) (i : α)
    --   :
    --     (graph.nodesInto i).card ≥ 1 :=
    --   sorry
    --   let j : Fin n := if i = ⟨0, by linarith⟩ then ⟨1, by linarith⟩ else ⟨0, by linarith⟩
    --   have : i.1 ≠ j.1 := sorry
    --   match (hc j i).some with
    --   | .cons _ k w i h => sorry

  end
  end SimpleGraph
end
