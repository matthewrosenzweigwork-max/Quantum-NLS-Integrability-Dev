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

def spectralPolynomial {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  (n:ℂ)*Real.pi +
    ∑ k ∈ Finset.Icc 1 (N+1),
      NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k /
        (n:ℂ)^k

end
end NlsGge.ThirdConsultation.KSPS
