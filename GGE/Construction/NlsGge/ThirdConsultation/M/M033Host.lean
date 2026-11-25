import Mathlib
import NlsGge.ThirdConsultation.M.M021Host
import NlsGge.ThirdConsultation.M.M031Host
import NlsGge.Atomic.M.M005
import NlsGge.Atomic.M.M054
import NlsGge.GK38.Defs

   
                                                                                                                    

                                                                                                                     
                                                                                                                
                                                                                                       
                                                                                                  
                                                                                                                   
  

set_option autoImplicit false

noncomputable section

open NlsGge.GK38

namespace NlsGge.ThirdConsultation.MTwoMode

/-- Only define the H1 value on an actual H1 carrier. -/
def H1Norm (u : M.SobolevR 1) : ℝ :=
  potentialCoefficientNorm M.sourceH1Weight (realSlice (M.physicalOfSobolev u))

end NlsGge.ThirdConsultation.MTwoMode

namespace NlsGge.ThirdConsultation.M

/-- Exact source low threshold; a strict inequality, with no L2 replacement. -/
def LowModeH1Threshold (u : SobolevR 1) (n : ℤ) : Prop :=
  NlsGge.Atomic.M.M054.indexWeight n < 8 * MTwoMode.H1Norm u ^ 2

/-- The nonzero label is part of the source two-sided comparison. -/
def HighModeH1Threshold (u : SobolevR 1) (n : ℤ) : Prop :=
  n ≠ 0 ∧ 8 * MTwoMode.H1Norm u ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n

end NlsGge.ThirdConsultation.M

end
