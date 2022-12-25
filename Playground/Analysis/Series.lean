import Mathlib



structure Series where
  sequence : ℕ → ℝ

namespace Series
open Topology


def TendsTo (s : Series) (l : ℝ) := Filter.Tendsto s.sequence ⊤ (𝓝 l)


end Series
