import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch

namespace Analysis.Roots

noncomputable def squareRoot (x : ℝ) : ℝ :=
  let S := { r : ℝ | r * r ≥ x }
  let y := if x ≤ 1 then 1 else x
  have hy : y ∈ S :=
    if hx : x ≤ 1 then by
      dsimp
      rw [if_pos hx]
      simp
      assumption
    else by
      dsimp
      rw [if_neg hx]
      have hx : x ≥ 1 := le_of_not_ge hx
      have : x > 0 := lt_of_lt_of_le zero_lt_one hx
      have := (mul_le_mul_right this).mpr hx
      rw [one_mul] at this
      exact this
  have hS : BddAbove S := ⟨0, sorry⟩
  let r := Real.exists_isLUB S ⟨y, hy⟩ hS
  r.choose

example (s : Set ℝ) (a : ℝ) (ha : IsLUB s a) : supₛ s = a :=
  by
  dsimp [supₛ]
  if h : s.Nonempty ∧ BddAbove s then
    rw [dif_pos h]
    let z := Classical.choose ⟨a, ha⟩
    have hz := Classical.choose_spec ⟨a, ha⟩
    exact IsLeast.unique hz ha
  else
    rw [dif_neg h]
    sorry

set_option trace.Meta.synthInstance true

noncomputable 
example [ConditionallyCompleteLinearOrder L] : CompleteLinearOrder $ WithBot (WithTop L) := inferInstance

end Analysis.Roots