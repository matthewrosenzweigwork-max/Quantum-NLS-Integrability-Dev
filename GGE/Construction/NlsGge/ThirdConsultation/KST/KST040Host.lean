import Mathlib
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST027
import NlsGge.ThirdConsultation.KST.KST034Host

                                                                                                                    
                                                                                                         
                                                                                                          
                                                                                                                     
                                                                                                                
                                                                                                               
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

def coefficientInvolution (ε : ℝ) (r : RawPair) : RawPair :=
  fun channel m => (ε : ℂ) * star (r (!channel) (-m))

def weightedInvolution (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (ε : ℝ) (x : Weighted ω) : Weighted ω :=
  weightedLift ω (coefficientInvolution ε (weightedCoeffs ω x))

end NlsGge.ThirdConsultation.KST
end
