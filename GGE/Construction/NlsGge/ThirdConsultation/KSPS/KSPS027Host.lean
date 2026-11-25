import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS015Host
import NlsGge.ThirdConsultation.KSPS.KSPS020Host
import NlsGge.ThirdConsultation.KSPS.KSPS023Host

                                                                                                              
                                                                                                                 
                                                                                                                        
                                                                                                                 
                                                                                                          
                                                                                                                         
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common NlsGge.ThirdConsultation
open NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def UnorderedEndpointExpansion (N : ℕ) (φ : SobolevC N) (s : ℝ) : Prop :=
  ∃ eplus eminus : ℤ → ℂ,
    WeightedL2Error s eplus ∧ WeightedL2Error s eminus ∧
    ∀ᶠ n : ℤ in Filter.cocompact ℤ,
      ({periodicMinus φ n, periodicPlus φ n} : Multiset ℂ) =
        {spectralPolynomial φ n +
            Complex.sqrt
              (physicalFourier (toPotPair φ).1 (-n) *
               physicalFourier (toPotPair φ).2 n) + eplus n,
         spectralPolynomial φ n -
            Complex.sqrt
              (physicalFourier (toPotPair φ).1 (-n) *
               physicalFourier (toPotPair φ).2 n) + eminus n}

end
end NlsGge.ThirdConsultation.KSPS
