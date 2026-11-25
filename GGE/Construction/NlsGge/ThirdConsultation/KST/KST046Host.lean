import Mathlib
import NlsGge.Atomic.DM.DM046
import NlsGge.Atomic.KST.KST043
import NlsGge.ThirdConsultation.KST.Basic

                                                                                                                    
                                                                                                              
                                                                                                                      
                                                                                                                 
                                                                                                      
                                                                                       
                                                        
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST043 NlsGge.Atomic.DM046

namespace NlsGge.ThirdConsultation.KST

def ExponentialWeight (ω : ℤ → ℝ) (χ : ℝ) : Prop :=
  AdmissibleWeight ω ∧ SubmultiplicativeWeight ω ∧ 0 < χ ∧
  Tendsto (KSTLogRatio ω) atTop (𝓝 χ)

def expWeight (ε : ℝ) (k : ℤ) : ℝ := Real.exp (ε * (k.natAbs : ℝ))

end NlsGge.ThirdConsultation.KST
end
