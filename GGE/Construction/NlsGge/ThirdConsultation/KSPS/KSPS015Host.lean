import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.ThirdConsultation.KSPSInversePhaseHost
import NlsGge.GK38.PairRealBridge

                                                                                                              
                                                                                                                   
                                                                                                                    
                                                                                                               
                                                                                                    
                                                             
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
