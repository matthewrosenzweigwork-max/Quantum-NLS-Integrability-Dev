import Mathlib
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.StdRootBranchesDefs

                                                                                                                  
                                                                                                               
                                                                                                                       
                                                                               
                                                                                                                       
                                                                          
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

def criticalOmittedFactor (n k : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  if k = n then 1 else
    (lamDot φ k - z) / stdRoot38 (tauN φ k) (gamma2 φ k) z

def criticalOmittedProduct (n : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  ∏' k : ℤ, criticalOmittedFactor n k φ z

end
end NlsGge.ThirdConsultation.KSN
