import Mathlib
import NlsGge.Spectral.ReservedEnergyCoercivity38V1

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Schur
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.Atomic.S050

/-- S050.02: source wrapper for the large-H1 estimate, including the zero mode. -/
theorem Q2_ge_large_H1 (N : ℕ) (z : FourierPlane N) (R : ℝ)
    (hR : 1 ≤ R) (hz : R ≤ planeH1Norm38 N z) :
    (1 / 4 : ℝ) * R ^ 2 ≤ localCharge38 (planeReal N z) 1 := by
  have h := planeQ2_ge_H1_sq38 N z R hR hz
  linarith

end NlsGge.Atomic.S050
