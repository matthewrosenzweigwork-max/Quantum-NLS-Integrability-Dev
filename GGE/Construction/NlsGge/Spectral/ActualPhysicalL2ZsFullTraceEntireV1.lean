import NlsGge.Spectral.ActualPhysicalL2ZsDysonTsumEntireV3
import Mathlib.LinearAlgebra.Matrix.Trace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The full trace of the actual rough fundamental matrix is entire. The
time endpoint is explicit, so unit and doubled monodromies stay distinct. -/
theorem analyticOnNhd_actualPhysicalL2ZsFullTrace
    (u : PhysicalL2) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => Matrix.trace (actualComplexZsDysonTsum
        (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
        z t)) Set.univ := by
  simpa only [Matrix.trace_fin_two] using!
    (analyticOnNhd_actualPhysicalL2ZsDysonTsum u t ht 0 0).add
      (analyticOnNhd_actualPhysicalL2ZsDysonTsum u t ht 1 1)

end NlsGge.SpectralFoundations
end
