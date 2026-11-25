import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS015Host

/- KSPS-017 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS017Host.lean.
   Bodies VERBATIM from Pro round 14 (PRO_DEFINITION_RESPONSE_FP80_14.md Cluster 1 = followup12 DEFINITIONS/KSPS.lean.md
   "Round-14 replacement bodies"): KSPSWKB.phaseDerivative, KSPSWKB.discriminantDerivativeMain.
   grep of NlsGge/ (2026-11-01): no declaration of either name in namespace NlsGge.ThirdConsultation.KSPSWKB
   (LIB032 has an unrelated `phaseDerivative` on H1Pair in another namespace, not opened here).
   Header opens = Pro's block. LEXICAL REPAIR (as in KSPS012Host/KSPS014Host/KSPS016Host): Lean-3
   `local attribute [instance] Classical.propDecidable` -> `attribute [local instance] Classical.propDecidable`.
   Uses KSPS015Host (wkbPhase; integralRiccatiLeft via KSPSInversePhaseHost). -/

set_option autoImplicit false
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section
attribute [local instance] Classical.propDecidable

def phaseDerivative {N : ℕ} (φ : SobolevC N) (lam : ℂ) : ℂ :=
  1 - Complex.I * ∑ k ∈ Finset.Icc 1 N,
    (k : ℂ) * (2 * Complex.I) ^ (-(k : ℤ)) *
      lam ^ (-((k + 1 : ℕ) : ℤ)) * integralRiccatiLeft φ k

def discriminantDerivativeMain (N : ℕ) (φ : SobolevC N)
    (xi : ℤ → ℂ) (n : ℤ) : ℂ :=
  -2 * Complex.sin (wkbPhase φ (xi n)) * phaseDerivative φ (xi n) +
    (2 * Complex.I * (-1 : ℂ) ^ (n + 1)) /
      (2 * Complex.I * xi n) ^ (N + 1) *
        integralRiccatiLeft φ (N + 1)

end
end NlsGge.ThirdConsultation.KSPSWKB
