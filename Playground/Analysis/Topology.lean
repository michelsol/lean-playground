import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Real.ENNReal
import Mathlib.Topology.MetricSpace.Basic

-- set_option trace.Meta.synthInstance true
example : InfSet (Filter α) := inferInstance

example (f : α → β) (g : β → γ) (a : Filter α) (b : Filter β) (c : Filter γ) 
  (hf : Filter.Tendsto f a b) (hg : Filter.Tendsto g b c) : Filter.Tendsto (g ∘ f) a c := by
    intro z hz
    -- show g ⁻¹' z ∈ Filter.map f a
    exact hf $ hg hz


open scoped ENNReal NNReal

section
  variable {E} [EMetricSpace E]
  namespace EMetricSpace
  abbrev Set := _root_.Set

  def openBall (center : E) (radius : ℝ≥0∞) := EMetric.ball center radius

  def closedBall (center : E) (radius : ℝ≥0∞) := { x : E | edist x center ≤ radius }

  def sphere (center : E) (radius : ℝ≥0∞) := { x : E | edist x center = radius }

  def Set.interior (s : Set E) := { c : E | ∃ r > 0, openBall c r ⊆ s }

  def Set.IsOpen (s : Set E) := s ⊆ s.interior

  def Set.closure (s : Set E) := { c : E | ∀ r > 0, (openBall c r ∩ s).Nonempty }

  def Set.IsClosed (s : Set E) := s.closure ⊆ s

  def neighborhood (x : E) := { s : Set E | x ∈ s.interior }
  
  def 𝓝 (x : E) : Filter E where
    sets := { s : Set E | x ∈ s.interior }
    univ_sets := by
      use 1
      simp
    sets_of_superset := by
      intro X Y ⟨r, hr⟩ hXY
      use r
      constructor
      . exact hr.1
      . intro z hz
        exact hXY $ hr.2 hz
    inter_sets := by
      intro X Y ⟨r, hr⟩ ⟨s, hs⟩
      let t := min r s
      use t
      sorry


  def Set.clusterPoint (s : Set E) := { x : E | x ∈ (s \ {x}).closure }

  def Set.isolatedPoint (s : Set E) := { x ∈ s | x ∉ (s \ {x}).closure }

  theorem Set.openBall.center_mem (c : E) (r : ℝ≥0∞) (rp : r > 0) : c ∈ openBall c r :=
    show edist .. < _ from edist_self c ▸ rp

  theorem Set.sub_closure (s : Set E) : s ⊆ s.closure :=
    λ x hx r rp => ⟨x, ⟨openBall.center_mem x r rp, hx⟩⟩

  theorem Set.IsClosed.closure_eq {s : Set E} (hs : s.IsClosed) : s.closure = s :=
    Set.eq_of_subset_of_subset hs s.sub_closure

  theorem Set.interior_sub (s : Set E) : s.interior ⊆ s :=
    λ x ⟨r, rp, hxs⟩ => hxs (openBall.center_mem x r rp)

  theorem Set.IsOpen.interior_eq {s : Set E} (hs : s.IsOpen) : s.interior = s :=
    Set.eq_of_subset_of_subset s.interior_sub hs

  theorem Set.interior_compl (s : Set E) : s.interiorᶜ = sᶜ.closure := by
    ext c
    show (¬∃ _, _) ↔ ∀ _, _
    push_neg
    rw [forall_congr']
    intro x
    rw [imp_congr_right]
    intro _
    rw [Set.not_subset]
    rfl

  theorem Set.isOpen_iff_compl_isClosed (s : Set E) : s.IsOpen ↔ sᶜ.IsClosed := by
    dsimp [IsOpen, IsClosed]
    rw [←Set.compl_subset_compl, interior_compl]


  -- converse is false
  theorem Set.interior_unionₛ_sub (c : Set (Set E)) : ⋃₀ c.image interior ⊆ Set.interior (⋃₀ c) := by
    intro x ⟨sₒ, ⟨⟨s, hs, hs₀⟩, hxs⟩⟩
    rw [←hs₀] at hxs
    let ⟨r, rp, hr⟩ := hxs
    use r
    constructor
    . exact rp
    . intro y hy
      use s
      constructor
      . exact hs
      . exact hr hy

  -- converse is true in the finite case
  theorem Set.interₛ_interior_sub (c : Set (Set E)) : Set.interior (⋂₀ c) ⊆ ⋂₀ c.image interior := by
    intro x ⟨r, rp, hr⟩
    intro sₒ ⟨s, hs, hsₒ⟩
    rw [←hsₒ]
    use r
    constructor
    . exact rp
    . intro y hy
      exact hr hy _ hs

  theorem Set.interior_inter_sub (s₁ s₂ : Set E) : s₁.interior ∩ s₂.interior ⊆ (s₁ ∩ s₂).interior := by
    intro x ⟨⟨r₁, rp₁, h₁⟩, ⟨r₂, rp₂, h₂⟩⟩
    -- let r := min r₁ r₂
    sorry

  -- converse is false
  theorem Set.interₛ_closure_sub (c : Set (Set E)) : Set.closure (⋂₀ c) ⊆ ⋂₀ c.image closure := by
    intro x hx 
    intro s_bar ⟨s, hs⟩ 
    rw [←hs.2]
    intro r rp
    let ⟨y, hy⟩ := hx r rp
    use y
    constructor
    . exact hy.1
    . exact hy.2 s hs.1

  -- theorem Set.IsOpenUnionₛ (c : Set (Set E)) (h : ∀ s ∈ c, s.IsOpen) : IsOpen (⋃₀ c) := 
  --   flip subset_trans c.interior_unionₛ_sub $ Set.unionₛ_subset_unionₛ λ s hs => ⟨s, ⟨hs, (h s hs).interior_eq⟩⟩

  -- theorem Set.IsClosedInterₛ (c : Set (Set E)) (h : ∀ s ∈ c, s.IsClosed) : IsClosed (⋂₀ c) := 
  --   c.interₛ_closure_sub.trans $ Set.interₛ_subset_interₛ λ s hs => ⟨s, ⟨hs, (h s hs).closure_eq⟩⟩


  def Function.TendsTo {E F} [EMetricSpace E] [EMetricSpace F] (f : E → F) (a : E) (l : F) := 
    ∀ V ∈ neighborhood l, ∃ U ∈ neighborhood a, U.image f ⊆ V

  end EMetricSpace
end
