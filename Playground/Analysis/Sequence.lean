import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Tactic.Linarith
-- import Mathlib.Data.Real.Basic
-- import Playground.Analysis.Topology

def Sequence := ℕ → ℝ

namespace Sequence
def of (u : ℕ → ℝ) : Sequence := u

section
  variable (u : Sequence)
  def TendsTo (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

  def IsCauchy := ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, |u n - u m| < ε

  def Increasing := ∀ n, u n ≤ u (n + 1)

  def Decreasing := ∀ n, u (n + 1) ≤ u n

  def image := Set.univ.image u

  def BoundedAbove := BddAbove u.image

  def BoundedBelow := BddBelow u.image

  def Bounded := u.BoundedAbove ∧ u.BoundedBelow
end

namespace IsCauchy
section
  variable {u : Sequence}
  theorem boundedAbove : u.IsCauchy → u.BoundedAbove := λ hu =>
    let ⟨N, h⟩ := hu 1 zero_lt_one
    have h := h N (le_refl _)
    let b := (u N) + 1
    have hb := by
      intro r ⟨n, ⟨_, hr⟩⟩
      rw [←hr]
      dsimp; have h := h
      sorry
    ⟨b, hb⟩

  theorem boundedBelow : u.IsCauchy → u.BoundedAbove := sorry

  theorem bounded : u.IsCauchy → u.Bounded := sorry

  noncomputable def limit : u.IsCauchy → ℝ := sorry
  
  theorem tendsTo_limit (hu : u.IsCauchy) : u.TendsTo hu.limit := sorry
end
end IsCauchy

section
  variable {u : Sequence}
  theorem TendsTo.isCauchy {l} : u.TendsTo l → u.IsCauchy := sorry

  theorem TendsTo.bounded {l} : u.TendsTo l → u.Bounded := λ h => h.isCauchy.bounded

  noncomputable def BoundedAbove.imageSup : u.BoundedAbove → ℝ := λ h => 
    (Real.exists_isLUB u.image ⟨u 0, ⟨0, ⟨⟨⟩, rfl⟩⟩⟩ h).choose

  theorem BoundedAbove.Increasing.tendsTo_imageSup (h : u.BoundedAbove) : u.Increasing →
    u.TendsTo h.imageSup := sorry

  noncomputable def BoundedBelow.imageInf : u.BoundedBelow → ℝ := sorry

  theorem BoundedBelow.Decreasing.tendsTo_imageInf (h : u.BoundedBelow) : u.Decreasing →
    u.TendsTo h.imageInf := sorry
end

def Constant (c : ℝ) := of λ _ => c

def le (u v : Sequence) := ∀ n, u n ≤ v n
instance : LE Sequence where le := le


end Sequence


-- noncomputable def Set.closure.sequence {s : Set ℝ} {x : ℝ} (hx : s.closure x)
--   : Sequence :=
--   λ n => 
--     let r := (1 : ℝ) / n
--     (hx r sorry).choose

-- theorem Set.closure.sequence_tendsTo {s : Set ℝ} {x : ℝ} (hx : s.closure x)
--   : hx.sequence.TendsTo x :=
--   sorry
