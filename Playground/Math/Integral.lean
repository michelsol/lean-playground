import Mathlib


section
open Interval
open BigOperators
namespace Real

structure Subdivision (a b : ℝ) (n : ℕ) where
  map : Fin (n + 1) → ℝ
  map_0 : map 0 = a
  map_n : map n = b
  sorted : StrictMono map

instance : CoeFun (Subdivision a b n) (λ _ => Fin (n + 1) → ℝ) := ⟨Subdivision.map⟩

def Subdivision.interval (s : Subdivision a b n) : Fin n → Set ℝ :=
  λ k => Set.Icc (s k) (s (k + 1))

theorem Subdivision.interval_sub (s : Subdivision a b n) : ∀ k, s.interval k ⊆ Set.Icc a b := by
  intro k
  intro x (hx : x ∈ Set.Icc _ _)
  rw [Set.mem_Icc] at hx ⊢
  constructor
  . rw [←s.map_0]
    apply le_trans _ hx.1
    exact s.sorted.monotone k.zero_le
  . rw [←s.map_n]
    apply hx.2.trans
    apply s.sorted.monotone
    exact (k + 1 : Fin (n + 1)).le_val_last

structure PiecewiseConstantMap (a b : ℝ) where
  map : Set.Icc a b → ℝ
  {n : ℕ}
  σ : Subdivision a b n
  c : Fin n → ℝ
  prop : ∀ k, ∀ x, ∀ hx : x ∈ σ.interval k, map (⟨x, σ.interval_sub k hx⟩) = c k

instance : CoeFun (PiecewiseConstantMap a b) (λ _ => Set.Icc a b → ℝ) := ⟨PiecewiseConstantMap.map⟩

def PiecewiseConstantMap.integral (f : PiecewiseConstantMap a b) :=
  ∑ k : Fin f.n, (f.σ (k + 1) - f.σ k) * f.c k

def PiecewiseConstantMap.ofConstant (hab : a < b) (c₀ : ℝ) : PiecewiseConstantMap a b where
  map _ := c₀
  n := 1
  σ := {
    map := λ
      | 0 => a
      | 1 => b
    map_0 := rfl
    map_n := rfl
    sorted := λ
      | 1, 1, _ => by contradiction
      | 0, 1, _ => hab
  }
  c _ := c₀
  prop _ _ _ := rfl

  theorem PiecewiseConstantMap.integral_ofConstant (hab : a < b) (c₀ : ℝ)
    : (ofConstant hab c₀).integral = (b - a) * c₀ := by
    simp [integral, ofConstant] -- bad
    left
    rfl


end Real
end

section

def MeasurableSpace.map2 (f : α → β) (m : MeasurableSpace α) : MeasurableSpace β where
  MeasurableSet' s := MeasurableSet (f ⁻¹' s)
  measurableSet_empty := m.measurableSet_empty
  measurableSet_compl s hs := m.measurableSet_compl _ hs
  measurableSet_iUnion g hg := by
    -- dsimp
    -- dsimp [MeasurableSet]
    simp only [Set.preimage_iUnion] --using sorry
    sorry
  -- measurableSet_iUnion g hg := by
  --   show MeasurableSet (_ ⁻¹' ⋃ _, _)
  --   rw [Set.preimage_iUnion]
  --   apply m.measurableSet_iUnion (f ⁻¹' g .)
  --   exact hg

end
