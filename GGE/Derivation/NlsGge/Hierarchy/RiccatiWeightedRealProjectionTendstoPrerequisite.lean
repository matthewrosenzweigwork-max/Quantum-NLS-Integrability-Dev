import NlsGge.Sobolev.PhysicalProjection
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.Pilot

open Filter
open scoped Topology

theorem weightedRealProjection_tendsto_actual
    {w : ℤ → ℝ} [Fact (∀ n : ℤ, 0 < w n)] (x : WeightedRealHilbert w) :
    Filter.Tendsto
      (fun N : ℕ => weightedRealProjectionContinuous w (symmetricModes N) x)
      Filter.atTop (nhds x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := (Metric.tendsto_nhds.mp
    (weightedProjection_tendsto w (show WeightedHilbert w from x))) ε hε
  filter_upwards [h] with N hN
  simpa [weightedRealProjectionContinuous, weightedRealProjectionLinear] using! hN

end NlsGge.Pilot
