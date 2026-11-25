import Mathlib
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST027
import NlsGge.ThirdConsultation.KST.KST034Host

                                                                                                                    
                                                                                                                 
                                                                                                           
                                                                                                                
                                                                                                             
                                                                                                    
                        
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

def truncateCoefficients (J : ℕ) (r : RawPair) : RawPair :=
  fun channel m => if m.natAbs ≤ J then r channel m else 0

def truncateWeighted (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (J : ℕ) (x : Weighted ω) : Weighted ω :=
  weightedLift ω (truncateCoefficients J (weightedCoeffs ω x))

end NlsGge.ThirdConsultation.KST
end
