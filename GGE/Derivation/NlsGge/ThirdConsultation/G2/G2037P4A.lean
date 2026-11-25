import Mathlib

set_option autoImplicit false

open Set Filter Topology Metric Complex MeasureTheory
open scoped Real

namespace NlsGge.G2037P5
noncomputable section

/-- A closed segment in `ℂ` is closed (it is the convex hull of two points). -/
theorem segment_isClosed_G2037P5 (a b : ℂ) : IsClosed (segment ℝ a b) := by
  rw [← convexHull_pair]
  have hfin : ({a, b} : Set ℂ).Finite := Set.toFinite _
  have hc : IsCompact (convexHull ℝ ({a, b} : Set ℂ)) := hfin.isCompact_convexHull ℝ
  exact hc.isClosed

/-- The finite union of the gap segments `segment ℝ (a n) (b n)`, `n ∈ S`, is closed. This is
the closedness hypothesis needed for the complement `finiteGapCuts ᶜ` to be open. -/
theorem cuts_isClosed_G2037P5 (a b : ℤ → ℂ) (S : Finset ℤ) :
    IsClosed (⋃ n ∈ (S : Set ℤ), segment ℝ (a n) (b n)) :=
  (S.finite_toSet).isClosed_biUnion (fun n _ => segment_isClosed_G2037P5 (a n) (b n))

end

end NlsGge.G2037P5
