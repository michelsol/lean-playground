import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Playground.Data.GeneralDotNotation

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

  def finMapExcluding : (a : Fin (n + 1)) → { x : Fin (n + 1) // x ≠ a } → Fin n
    | ⟨a, a_lt⟩, ⟨⟨i, i_lt⟩, i_prop⟩ =>
      have : i ≠ a := λ c => i_prop (Fin.eq_of_val_eq c)
      if hi : i ≤ a then
        have := lt_of_le_of_ne hi this
        { val := i, isLt := by linarith }
      else
        have : i > 0 := by linarith
        { val := i - 1, isLt := by zify [this]; linarith }

  theorem finMapExcluding_injective : ∀ a : Fin (n + 1), (finMapExcluding a).Injective
    | ⟨a, a_lt⟩, ⟨⟨i, i_lt⟩, i_prop⟩, ⟨⟨j, j_lt⟩, j_prop⟩, (h : dite .. = dite ..) =>
      if hi : i ≤ a then
        if hj : j ≤ a then by
          simp [hi, hj] at h
          subst h; rfl
        else by
          simp [hi, hj] at h
          have : j > 0 := by linarith
          zify [this] at h
          have : i = a := by linarith
          subst this; contradiction
      else 
        if hj : j ≤ a then by
          simp [hi, hj] at h
          have : i > 0 := by linarith
          zify [this] at h
          have : j + 1 = i := by linarith
          have : j = a := by linarith
          subst this; contradiction
        else by
          simp [hi, hj] at h
          have i_pos : i > 0 := by linarith
          have j_pos : j > 0 := by linarith
          zify [i_pos, j_pos] at h
          have : i = j := by linarith
          subst this; rfl

  theorem le_of_injective {f : Fin n → Fin m} (hf : Injective f) : n ≤ m :=
    match n, m with
    | 0, _ => Nat.zero_le _
    | _ + 1, 0 => (Nat.not_lt_zero _ (f ⟨0, Nat.zero_lt_succ _⟩).isLt).elim
    | n + 1, m + 1 =>
      let a := f { val := n, isLt := by linarith }
      let g₁ : Fin n → { x : Fin (m + 1) // x ≠ a } :=
        λ { val := i, isLt := i_lt_n } => {
          val := f { val := i, isLt := by linarith }
          property := λ c => Nat.ne_of_lt i_lt_n $ Fin.val_eq_of_eq $ hf c
        }
      have hg₁ : Injective g₁ := λ i j h =>
        have := Fin.val_eq_of_eq $ hf $ congrArg Subtype.val h
        Fin.eq_of_val_eq this
      let hg₂ := finMapExcluding_injective a
      Nat.succ_le_succ <| le_of_injective <| Injective.comp hg₂ hg₁

  theorem ge_of_surjective {f : Fin n → Fin m} (hf : Surjective f) : n ≥ m :=
    right_inverse.is_injective hf |> le_of_injective

  theorem eq_of_bijective {f : Fin n → Fin m} (hf : Bijective f) : n = m := 
    (le_of_injective hf.injective)·le_antisymm (ge_of_surjective hf.surjective)

example (a b : ℕ) (h : a ≤ b) (g : b ≤ a) : a = b := by
  -- linarith
  sorry
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