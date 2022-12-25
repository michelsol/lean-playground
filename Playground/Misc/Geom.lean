import Mathlib

namespace Geom
structure Point where
  x : ℝ
  y : ℝ

structure Vector where
  x : ℝ
  y : ℝ

def Point.add (u : Point) (v : Vector) : Point where
  x := u.x + v.x
  y := u.y + v.y
instance : HAdd Point Vector Point := ⟨Point.add⟩

def Point.sub (u v : Point) : Vector where
  x := u.x - v.x
  y := u.y - v.y
instance : HSub Point Point Vector := ⟨Point.sub⟩

def Vector.add (u v : Vector) : Vector where
  x := u.x + v.x
  y := u.y + v.y
instance : Add Vector := ⟨Vector.add⟩

def Vector.sub (u v : Vector) : Vector where
  x := u.x - v.x
  y := u.y - v.y
instance : Sub Vector := ⟨Vector.sub⟩

def Vector.norm2 (u : Vector) := u.x * u.x + u.y * u.y

def Point.distance (u v : Point) := (v - u).norm2

open NNReal

def circle (c : Point) (r : ℝ≥0) := { x | c.distance x = r }
def unitCircle := circle ⟨0, 0⟩ 0

open ENat

noncomputable
def arcLength {a b : ℝ} (hab : a < b) (f : ℝ → ℝ×ℝ) := ∫ t in Set.Icc a b, ‖deriv f t‖

example (hab : a < b) : arcLength hab (λ t => (t, t)) = 0 := by
  dsimp [arcLength]
  sorry


open Asymptotics
example (f : ℝ → ℝ × ℝ) (x : ℝ) (hf : HasDerivAt f f' x) :
  HasDerivAt (fst ∘ f) f'.1 x := by
  let ff' := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) f'
  have hf : HasFDerivAt f ff' x := hf.hasFDerivAt
  show HasFDerivAt ..
  dsimp [HasFDerivAt, HasFDerivAtFilter] at hf ⊢
  rw [IsLittleO_def] at hf ⊢
  simp only [IsBigOWith_def] at hf ⊢
  intro ε hε
  have hf := hf hε
  dsimp [norm] at hf ⊢
  sorry


example [Fintype I] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : E → I → F) (f' : E →L[𝕜] I → F) (x : E) (hf : HasFDerivAt f f' x) (i : I) :
  HasFDerivAt (f . i) ((ContinuousLinearMap.proj i).comp f') x := by
  dsimp [HasFDerivAt, HasFDerivAtFilter] at hf ⊢
  rw [IsLittleO_def] at hf ⊢
  simp only [IsBigOWith_def] at hf ⊢
  intro ε hε
  have hf := hf hε
  dsimp [norm] at hf ⊢
  sorry

end Geom
