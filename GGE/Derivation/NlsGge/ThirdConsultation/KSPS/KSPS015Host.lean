import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.ThirdConsultation.KSPSInversePhaseHost
import NlsGge.GK38.PairRealBridge

/- KSPS-015 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS015Host.lean.
   Bodies VERBATIM from the round-14 active page followup12 DEFINITIONS/KSPS.lean.md, "Retained design-only bodies"
   (`NlsGge.ThirdConsultation.KSPS.WeightedL2Error`, `.discriminant`, `.wkbPhase`; Pro round 14 Cluster 1 says these
   "are hosted once with their existing bodies"). grep of NlsGge/ (2026-11-01) found none of the three names in
   namespace NlsGge.ThirdConsultation.KSPS (G1036 has an unrelated `wkbPhase` in another namespace).
   Header opens = Pro's block for those bodies. No repair. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common NlsGge.ThirdConsultation
open NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def WeightedL2Error (s : ℝ) (e : ℤ → ℂ) : Prop :=
  Summable (fun n : ℤ => indexWeight n^(2*s) * ‖e n‖^2)

end
end NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def discriminant {N : ℕ} (φ : SobolevC N) (lam : ℂ) : ℂ :=
  NlsGge.GK38.discrim (toPotPair φ) lam

end
end NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def wkbPhase {N : ℕ} (φ : SobolevC N) (lam : ℂ) : ℂ :=
  lam + Complex.I *
    ∑ k ∈ Finset.Icc 1 N,
      (2*Complex.I*lam)^ (-(k : ℤ)) * integralRiccatiLeft φ k

end
end NlsGge.ThirdConsultation.KSPS
