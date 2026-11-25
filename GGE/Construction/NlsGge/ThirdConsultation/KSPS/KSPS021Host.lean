import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS016Host
import NlsGge.ThirdConsultation.KSPS.KSPS019Host

                                                                                                              
                                                                                                                        
                                                                                                              
                                                                                                        
                                                                                                                
                                                                                      
                                                                                                                          
                                                                                                                    
                                            

set_option autoImplicit false
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section
attribute [local instance] Classical.propDecidable

-- Principal log gives the source's high-frequency branch near 1. This
-- definition makes no assertion that it equals the globally continued κ_n
-- at the finitely many low modes.
def normingLog (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℂ :=
  2 * Complex.log ((-1 : ℂ) ^ n *
    (discriminant φ (mu φ n) + antitrace φ (mu φ n)) / 2)

def normingError (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℂ :=
  normingLog N φ n - Complex.I *
    (physicalFourier (toPotPair φ).1 (-n) -
     physicalFourier (toPotPair φ).2 n)

end
end NlsGge.ThirdConsultation.KSPSWKB

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def DirichletBoundaryWeightedL2 (N : ℕ) (φ : SobolevC N) : Prop :=
  WeightedL2Error ((N + 1 : ℕ) : ℝ)
    (fun n : ℤ => discriminant φ (mu φ n) - 2 * (-1 : ℂ) ^ n) ∧
  WeightedL2Error ((N + 1 : ℕ) : ℝ) (KSPSWKB.normingError N φ)

end
end NlsGge.ThirdConsultation.KSPS
