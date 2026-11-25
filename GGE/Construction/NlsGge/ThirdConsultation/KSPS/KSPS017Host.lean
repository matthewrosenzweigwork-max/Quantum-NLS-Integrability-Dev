import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS015Host

                                                                                                              
                                                                                                                        
                                                                                               
                                                                                                            
                                                                                               
                                                                                                 
                                                                                                                
                                                                                

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
