import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Tactic.Linarith

variable {E} [PartialOrder E]
def segmentFrom (a : E) := { y : E | y ≤ a }
def openSegmentFrom (a : E) := { y : E | y < a }

def Set.IsSegment (S : Set E) := ∀ x : E, segmentFrom x ⊆ S

def Segments (E) [PartialOrder E] := { S : Set E | S.IsSegment }

example (h : IsWellOrder E (. ≤ .)) (S : Set E) (hS : S.IsSegment)
  (h2 : S ≠ Set.univ) : ∃ a, S = segmentFrom a :=
  by_contra $ λ c => by
  push_neg at c
  apply h2
  rw [Set.eq_univ_iff_forall]
  intro x
  have hc := c x
  sorry
