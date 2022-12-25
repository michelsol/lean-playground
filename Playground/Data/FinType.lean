import Mathlib.Logic.Function.Basic
import Playground.Data.GeneralDotNotation

section
  namespace Nat

  theorem pred_lt_of_lt_succ (ha : a ≠ 0) (h : a < b + 1) : a - 1 < b :=
    lt_of_succ_lt_succ $ (succ_pred ha).symm ▸ h

  theorem succ_eq_of_eq_pred (hb : b ≠ 0) (h : a = b - 1) : a + 1 = b :=
    succ_pred hb ▸ congrArg succ h

  end Nat
end

section
  namespace Function
  noncomputable def right_inverse_of_surjective {f : α → β} (h : Surjective f) 
    : β → α := 
    λ y => (h y).choose

  theorem right_inverse.is_RightInverse (h : Surjective f)
    : RightInverse (right_inverse_of_surjective h) f := 
    λ y => (h y).choose_spec

  theorem right_inverse.is_injective (h : Surjective f)
    : Injective (right_inverse_of_surjective h) :=
    (is_RightInverse h).injective

  end Function
end

section
  open Function

  def fin_map_excluding (a : Fin (n + 1)) : { x : Fin (n + 1) // x ≠ a } → Fin n := 
    open Nat in
    match a with | ⟨a, a_lt⟩ => λ ⟨⟨i, i_lt⟩, i_prop⟩ =>
      if hi : i ≤ a then
        have hi : i < a := lt_of_le_of_ne hi (λ c => i_prop $ Fin.eq_of_val_eq c)
        { val := i, isLt := lt_of_lt_of_le hi $ le_of_lt_succ a_lt }
      else have hi : a < i := Nat.lt_of_not_le hi
        { val := i - 1, isLt := 
          pred_lt_of_lt_succ (not_eq_zero_of_lt hi) i_lt }

  theorem injective_fin_map_excluding (a : Fin (n + 1)) : fin_map_excluding a |> Injective :=
    open Nat in by
    cases a with | mk a a_lt =>
    intro ⟨⟨i, i_lt⟩, i_prop⟩ ⟨⟨j, j_lt⟩, j_prop⟩ (h : dite .. = dite ..)
    apply Subtype.eq
    apply Fin.eq_of_val_eq
    show i = j
    exact
    if hi : i ≤ a then
      if hj : j ≤ a then by
        simp [hi, hj] at h
        exact h
      else by
        simp [hi, hj] at h
        have hj : a < j := Nat.lt_of_not_le hj
        have := succ_eq_of_eq_pred (not_eq_zero_of_lt hj) h
        rw [←this] at hj
        have := le_antisymm hi (le_of_lt_succ hj)
        exact (i_prop $ Fin.eq_of_val_eq this).elim
    else 
      if hj : j ≤ a then by
        simp [hi, hj] at h
        have hi : a < i := Nat.lt_of_not_le hi
        have := succ_eq_of_eq_pred (not_eq_zero_of_lt hi) h.symm
        rw [←this] at hi
        have := le_antisymm (le_of_lt_succ hi) hj
        exact (j_prop $ Fin.eq_of_val_eq this.symm).elim
      else by
        simp [hi, hj] at h
        have hi : a < i := Nat.lt_of_not_le hi
        have hj : a < j := Nat.lt_of_not_le hj
        exact Nat.pred_inj (Nat.zero_lt_of_lt hi) (Nat.zero_lt_of_lt hj) h

  theorem le_of_injective {f : Fin n → Fin m} (hf : Injective f) : n ≤ m :=
    open Nat Fin in
    match n, m with
    | 0, _ => zero_le _
    | _ + 1, 0 => (not_lt_zero _ (f ⟨0, zero_lt_succ _⟩).isLt).elim
    | n + 1, m + 1 =>
      let a := f { val := n, isLt := n.lt_succ_self }
      let g₁ : Fin n → { x : Fin (m + 1) // x ≠ a } :=
        λ { val := i, isLt := i_lt_n } => {
          val := f { val := i, isLt := i_lt_n·lt_trans n.lt_succ_self }
          property := λ c => Nat.ne_of_lt i_lt_n $ val_eq_of_eq $ hf c
        }
      have hg₁ : Injective g₁ := λ i j h =>
        have := val_eq_of_eq $ hf $ congrArg Subtype.val h
        eq_of_val_eq this
      let hg₂ := injective_fin_map_excluding a
      succ_le_succ <| le_of_injective <| Injective.comp hg₂ hg₁

  theorem ge_of_surjective {f : Fin n → Fin m} (hf : Surjective f) : n ≥ m :=
    right_inverse.is_injective hf |> le_of_injective

  theorem eq_of_bijective {f : Fin n → Fin m} (hf : Bijective f) : n = m :=
    (le_of_injective hf.injective)·le_antisymm (ge_of_surjective hf.surjective)
end

section
  open Function

  universe u
  variable (type : Type u)

  def has_card (n : Nat) := ∃ f : Fin n → type, Bijective f

  def is_finite := ∃ n, type·has_card n

  -- def Inhabited.has_card (type : Inhabited (Type u)) (n : Nat) := ∃ f : Fin n → type.default, bijective f
  -- def Inhabited.is_finite (type : Inhabited (Type u)) := ∃ n, type.has_card n

  noncomputable def card : Option Nat := 
    let this := Classical.propDecidable
    if h : type·is_finite then some h.choose
    else none

  theorem has_card_unique (hn : type·has_card n) (hm : type·has_card m) 
    : n = m :=
    let ⟨fn, hfn⟩ := hn
    let ⟨fm, hfm⟩ := hm
    sorry

end