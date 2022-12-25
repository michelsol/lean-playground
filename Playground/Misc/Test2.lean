import Mathlib
-- import Mathlib.Tactic.LibrarySearch

namespace List

section
  variable {α}

  section
    variable (p : α → Prop) [DecidablePred p]

    def beforeOrFirst  : List α → List α
      | [] => []
      | a :: l => if p a then [a] else a :: l.beforeOrFirst

    def afterFirst : List α → List α
      | [] => []
      | a :: l => if p a then l else l.afterFirst

    theorem beforeOrFirst_append_afterFirst
      (l : List α) : l.beforeOrFirst p ++ l.afterFirst p = l := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        show ite .. ++ ite .. = _
        by_cases h : p a
        . simp [h]
        . simp [h, ih]

    theorem afterFirst_Sublist (l : List α) : l.afterFirst p <+ l := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        show ite (p a) _ _ <+ _
        by_cases h : p a
        . rw [if_pos h]
          exact l.sublist_cons a
        . rw [if_neg h]
          exact ih.cons a

  end

  section
    variable [DecidableEq α]

    theorem mem_beforeOrFirst_of_mem (l : List α) {c} (h : c ∈ l)
      : c ∈ l.beforeOrFirst (. = c) := by
      induction l with
      | nil => contradiction
      | cons a l ih =>
        show c ∈ ite (a = c) _ _
        by_cases hac : a = c
        . rw [if_pos hac]
          simp [hac]
        . rw [if_neg hac]
          apply mem_cons_of_mem a
          apply ih
          exact mem_of_ne_of_mem (ne_comm.mp hac) h

    def removeCycles : List α → List α
      | [] => []
      | a :: l =>
        let lr := l.removeCycles
        if a ∈ lr then a :: lr.afterFirst (. = a) else a :: lr

    theorem removeCycles_Nodup (l : List α) : l.removeCycles.Nodup := by
      induction l with
      | nil => exact nodup_nil
      | cons a l ih =>
        let l := l.removeCycles
        have ih : l.Nodup := ih
        show (if a ∈ l then a :: _ else a :: l).Nodup
        by_cases hal : a ∈ l
        . rw [if_pos hal]
          apply nodup_cons.mpr
          constructor
          . let n := l.beforeOrFirst (. = a)
            let m := l.afterFirst (. = a)
            have hnm : n ++ m = l := l.beforeOrFirst_append_afterFirst (. = a)
            have han : a ∈ n := l.mem_beforeOrFirst_of_mem hal
            show a ∉ m
            rw [←hnm] at hal ih
            have hc := count_append a n m
            have := (n ++ m).count_eq_one_of_mem ih hal
            rw [this] at hc
            have := n.count_eq_one_of_mem ih.of_append_left han
            rw [this] at hc
            apply (m.count_eq_zero).mp
            exact Nat.add_left_cancel hc.symm
          . let m := l.afterFirst (. = a)
            show m.Nodup
            have := l.afterFirst_Sublist (. = a)
            exact ih.sublist this
        . rw [if_neg hal]
          apply nodup_cons.mpr
          exact ⟨hal, ih⟩

    theorem removeCycles_Sublist (l : List α) : l.removeCycles <+ l := by
      induction l with
      | nil => exact Sublist.slnil
      | cons a l ih =>
        let lr := l.removeCycles
        have ih : lr <+ l := ih
        show (if a ∈ lr then a :: lr.afterFirst (. = a) else a :: lr) <+ _
        by_cases ha : a ∈ lr
        . rw [if_pos ha]
          apply Sublist.cons₂
          have := lr.afterFirst_Sublist (. = a)
          exact Sublist.trans this ih
        . rw [if_neg ha]
          apply Sublist.cons₂
          exact ih

    -- #eval [3, 5, 3].removeCycles
    -- #eval [3, 5, 1].removeCycles
    -- #eval [3, 3, 5, 1].removeCycles
    -- #eval [3, 3, 3, 5, 1].removeCycles
    -- #eval [2, 3, 9, 7, 3, 3, 4, 3, 5, 1].removeCycles

  end

end

end List
