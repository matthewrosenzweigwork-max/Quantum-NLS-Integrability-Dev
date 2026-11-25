import Mathlib
import NlsGge.ThirdConsultation.M.MRound11Host
import NlsGge.ThirdConsultation.M.M021Host
import NlsGge.Atomic.M.M054

/-!
# M-029 host: `schurDet`, `localSpectralDisc` (proof development, host; not self-reviewed)

Definitions only, verbatim from Pro round 14 (`PRO_DEFINITION_RESPONSE_FP80_14.md`, Cluster 4, namespace
`NlsGge.ThirdConsultation.MTwoMode` block).  Landed objects (`schurMatrix`, `potentialCoefficientNorm`) are reused.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.MTwoMode

/-- Matrix determinant uses both landed diagonal entries, before their equality is proved. -/
def schurDet (φ : NlsGge.GK38.PotPair) (n : ℤ) (z : ℂ)
    (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n) : ℂ :=
  Matrix.det (schurMatrix φ n z hz)

/-- Closed disc, including the zero-radius free-potential case. -/
def localSpectralDisc (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) (n : ℤ) : Set ℂ :=
  Metric.closedBall ((n : ℂ) * (Real.pi : ℂ))
    (potentialCoefficientNorm w φ ^ 2 / NlsGge.Atomic.M.M054.indexWeight n +
      Real.sqrt 2 * potentialCoefficientNorm w φ /
        NlsGge.Atomic.M.M054.indexWeight (2 * n))

end NlsGge.ThirdConsultation.MTwoMode

end
