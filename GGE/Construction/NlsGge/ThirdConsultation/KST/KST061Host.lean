import Mathlib
import NlsGge.Atomic.KST.KST059
import NlsGge.ThirdConsultation.KST.KST034Host

                                                                                                                          
                                                                                                         
                                                                                                             
                                                                                                                    
                                                                                                                     
                                                                                        
                                                                                                                     
                                                                               
set_option autoImplicit false
noncomputable section
open NlsGge.GK38
open NlsGge.Atomic.KST059 (actualGapSequence)

namespace NlsGge.ThirdConsultation.KST

def FiniteFourierSupport (J : ℕ) (r : RawPair) : Prop :=
  ∀ channel m, J < m.natAbs → r channel m = 0

def pairFiniteGap (φ : PotPair) : Prop :=
  {n : ℤ | actualGapSequence φ n ≠ 0}.Finite

end NlsGge.ThirdConsultation.KST
end
