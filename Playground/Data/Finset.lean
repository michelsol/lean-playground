import Mathlib.Data.List.Perm

section
  universe u

  def MultiSet (α : Type u) := Quotient (α := List α) {
    r := List.Perm
    iseqv := List.Perm.Equivalence
  }

  namespace MultiSet

  def Nodup (s : MultiSet α) : Prop :=
    let rec th (l m : List α) (hlm : l ~ m) : List.Nodup l = List.Nodup m :=
      match l, m with
      | [], [] => rfl
      | a :: l, [] => sorry
      | [], b :: m => sorry
      | a :: l, b :: m => 
        have := th l m
        propext $
        show List.Pairwise (· ≠ ·) _ ↔ List.Pairwise (· ≠ ·) _ from
        {mp := λ h => 
        List.Pairwise.cons sorry sorry
        , mpr := sorry}

    Quot.liftOn s List.Nodup th

  end MultiSet


end

section
  universe u

  -- structure FinSet (α : Type u) where
  --   val : MultiSet α
  --   nodup : val.Nodup

end