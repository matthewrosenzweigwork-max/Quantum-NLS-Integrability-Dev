import Mathlib
import NlsGge.Atomic.M.M001

                                                                       
                                                                                         
                                                                                                                        
                                                                                                                            
set_option autoImplicit false
open scoped ENNReal
open NlsGge.Pilot

namespace NlsGge.ThirdConsultation.M
noncomputable section

def oddTraceSum (m : ℕ) (u : PhysicalL2) : ℝ :=
  ∑' n : ℤ, 4^m * higherAction u n (2*m+1)

def oddTraceEnergy (m : ℕ) (u : PhysicalL2) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal ((4 : ℝ) ^ m * higherAction u n (2 * m + 1))

end
end NlsGge.ThirdConsultation.M
