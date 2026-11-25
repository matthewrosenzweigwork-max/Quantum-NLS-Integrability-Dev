import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Host
import NlsGge.ThirdConsultation.KSPSInversePhaseHost

/- KSPS-012 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS012Host.lean.
   Bodies VERBATIM from Pro round 14 (PRO_DEFINITION_RESPONSE_FP80_14.md, Cluster 1, "integralRiccatiRight",
   "endpointDiagonalLower/Upper"). grep of NlsGge/ found none of integralRiccatiRight, endpointDiagonalLower,
   endpointDiagonalUpper. Header opens as in Pro's block (Matrix is needed by nothing here but kept). -/
set_option autoImplicit false
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

-- The left integral already exists in KSPSInversePhaseHost.
def integralRiccatiRight {N : ℕ} (φ : SobolevC N) (k : ℕ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    coverRep38 (toPotPair φ).2 x *
      coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.right φ k) x

end
end NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section
attribute [local instance] Classical.propDecidable

-- The diagonal adapters are RN_1 and SN_2. They are NOT entries of M-E.
def endpointDiagonalLower (N : ℕ) (φ : SobolevC N)
    (xi : ℤ → ℂ) (n : ℤ) : ℂ :=
  if hz : xi n = 0 then 0 else
    sourceRemainderVector φ false ⟨xi n, hz⟩ 1 0

def endpointDiagonalUpper (N : ℕ) (φ : SobolevC N)
    (xi : ℤ → ℂ) (n : ℤ) : ℂ :=
  if hz : xi n = 0 then 0 else
    sourceRemainderVector φ true ⟨xi n, hz⟩ 1 1

end
end NlsGge.ThirdConsultation.KSPSWKB
