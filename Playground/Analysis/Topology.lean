import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue



def Real.openBall (center : ℝ) (radius : ℝ) := { x : ℝ | |x - center| < radius }

def Real.closedBall (center : ℝ) (radius : ℝ) := { x : ℝ | |x - center| ≤ radius }

def Real.sphere (center : ℝ) (radius : ℝ) := { x : ℝ | |x - center| = radius }

def Set.interior (s : Set ℝ) := { c : ℝ | ∃ r > 0, c.openBall r ⊆ s }

def Set.IsOpen (s : Set ℝ) := s ⊆ s.interior

def Set.closure (s : Set ℝ) := { c : ℝ | ∀ r > 0, (c.openBall r ∩ s).Nonempty }

def Set.IsClosed (s : Set ℝ) := s.closure ⊆ s

def Real.neighborhood (x : ℝ) := { s : Set ℝ | x ∈ s.interior }

def Set.clusterPoint (s : Set ℝ) := { x : ℝ | x ∈ (s \ {x}).closure }

def Set.isolatedPoint (s : Set ℝ) := { x ∈ s | x ∉ (s \ {x}).closure }

theorem Set.interior_compl (s : Set ℝ) : s.interiorᶜ = sᶜ.closure := by
  ext c
  show (¬∃ _, _) ↔ ∀ _, _
  push_neg
  rw [forall_congr']
  intro x
  rw [imp_congr_right]
  intro _
  rw [not_subset]
  rfl

theorem Set.isOpen_iff_compl_isClosed {s : Set ℝ} : s.IsOpen ↔ sᶜ.IsClosed := by
  dsimp [IsOpen, IsClosed]
  rw [←compl_subset_compl]
  rw [interior_compl]


def Function.TendsTo (f : ℝ → ℝ) (a : ℝ) (l : ℝ) := 
  ∀ V ∈ l.neighborhood, ∃ U ∈ a.neighborhood, U.image f ⊆ V



theorem Set.IsOpen.eq_union_openBall {s : Set ℝ} (hs : s.IsOpen) 
  : ∃ I : Type, ∃ c : I → ℝ, ∃ r : I → ℝ, s = ⋃ i, (c i).openBall (r i) :=
  show ∃ I c r, s = {x | ∃ t, (∃ i, _) ∧ _} from
  ⟨{ x : ℝ // x ∈ s }, λ ⟨x, hx⟩ => x, λ ⟨x, hx⟩ => (hs hx).choose,
  ext λ x => ⟨
    λ hx =>
    let r := (hs hx).choose
    ⟨x.openBall r, ⟨⟨⟨x, hx⟩, rfl⟩, sorry⟩⟩
    , 
    by
    dsimp
    exact
    sorry⟩
  ⟩



namespace Analysis
namespace Topology

section
end

end Topology
end Analysis