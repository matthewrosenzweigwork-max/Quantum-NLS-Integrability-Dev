import NlsGge.GK38.MolnarMoments
import NlsGge.Spectral.F04LiteralBounds38

set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.SpectralFoundations
open NlsGge.HierarchyRiccati.Core NlsGge.GK38

namespace NlsGge.GK38

def MassChargeAllSobolevTarget38 : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ y : SobolevHilbert (m : ℝ),
    chargeSobolev38 (m + 1) 0 y = ‖sobolevToL2_38 m y‖ ^ 2

def MolnarActionSummabilityTarget38 : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ u : PhysicalL2,
    SobolevSquareSummable (m : ℝ) (physicalFourier u) →
      Summable (fun n : ℤ =>
        (1 + |2 * Real.pi * (n : ℝ)|) ^ (2 * m) * actualGapActionAllE02_38 u n)

end NlsGge.GK38
