import NlsGge.GK38.EigenvalueCompactnessWeakEndpoints
import NlsGge.GK38.EigenvalueCompactnessActionGlue

/-! # S7: norm continuity of both actual endpoints and every actual L2 gap action -/
set_option autoImplicit false
open Filter Topology
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem gapEndpoints_L2_continuous38 (n : ℤ) :
    Continuous (fun u : PhysicalL2 => actualGapLowerAllE02_38 u n) ∧
      Continuous (fun u : PhysicalL2 => actualGapUpperAllE02_38 u n) := by
  constructor
  · apply continuous_iff_seqContinuous.mpr
    intro u u₀ hu
    exact (gapEndpoints_weak_tendsto38 u u₀ (IsWeakLim.of_tendsto hu) n).1
  · apply continuous_iff_seqContinuous.mpr
    intro u u₀ hu
    exact (gapEndpoints_weak_tendsto38 u u₀ (IsWeakLim.of_tendsto hu) n).2

theorem gapAction_L2_continuous38 (n : ℤ) :
    Continuous (fun u : PhysicalL2 => actualGapActionAllE02_38 u n) :=
  gapAction_continuous_of_endpoints38 n (gapEndpoints_L2_continuous38 n).1 (gapEndpoints_L2_continuous38 n).2

end
end NlsGge.GK38
