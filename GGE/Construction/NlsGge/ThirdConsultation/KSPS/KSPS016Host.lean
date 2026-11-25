import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS014Host
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

def antitrace {N : ℕ} (φ : SobolevC N) (lam : ℂ) : ℂ :=
  monodromyPair (toPotPair φ) lam 0 1 +
    monodromyPair (toPotPair φ) lam 1 0

-- This is 2*i*chi_D, not chi_D itself.
def dirichletNumerator {N : ℕ} (φ : SobolevC N) (lam : ℂ) : ℂ :=
  monodromyPair (toPotPair φ) lam 1 1 +
    monodromyPair (toPotPair φ) lam 1 0 -
    monodromyPair (toPotPair φ) lam 0 1 -
    monodromyPair (toPotPair φ) lam 0 0

def antitraceError (N : ℕ) (φ : SobolevC N)
    (xi : ℤ → ℂ) (n : ℤ) : ℂ :=
  antitrace φ (xi n) -
    ((beta φ (xi n) 0 - alpha φ (xi n) 0) /
      (1 - alpha φ (xi n) 0 * beta φ (xi n) 0) *
        (2 * Complex.I * Complex.sin (wkbPhase φ (xi n))) +
     Complex.I * (-1 : ℂ) ^ n *
       (physicalFourier (toPotPair φ).1 (-n) -
        physicalFourier (toPotPair φ).2 n))

def dirichletError (N : ℕ) (φ : SobolevC N)
    (xi : ℤ → ℂ) (n : ℤ) : ℂ :=
  dirichletNumerator φ (xi n) -
    (((1 - alpha φ (xi n) 0) * (1 - beta φ (xi n) 0)) /
      (1 - alpha φ (xi n) 0 * beta φ (xi n) 0) *
        (2 * Complex.I * Complex.sin (wkbPhase φ (xi n))) +
     Complex.I * (-1 : ℂ) ^ (n + 1) *
       (physicalFourier (toPotPair φ).1 (-n) +
        physicalFourier (toPotPair φ).2 n) +
     2 * (-1 : ℂ) ^ (n + 1) /
       (2 * Complex.I * xi n) ^ (N + 1) *
        integralRiccatiLeft φ (N + 1))

end
end NlsGge.ThirdConsultation.KSPSWKB

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def AntiTraceDirichletWKB (N : ℕ) (φ : SobolevC N)
    (xi : ℤ → ℂ) : Prop :=
  WeightedL2Error ((N + 1 : ℕ) : ℝ)
    (KSPSWKB.antitraceError N φ xi) ∧
  WeightedL2Error ((N + 1 : ℕ) : ℝ)
    (KSPSWKB.dirichletError N φ xi)

end
end NlsGge.ThirdConsultation.KSPS
