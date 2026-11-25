import Mathlib
import NlsGge.Birkhoff.F08Bare38d

                                                                                                 
                                                                                                                   
                                                                                                                    
                                                                                                            
                                                                                                               
                                                                                                               
                                                                                                      
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure

namespace NlsGge.ThirdConsultation.F

def finiteOrderRelativeZ (m : ℕ) (β : ℕ → ℝ) (N : ℕ) : ℝ :=
  ZcalBare38 m β N / gaussConst38 m β N

end NlsGge.ThirdConsultation.F
