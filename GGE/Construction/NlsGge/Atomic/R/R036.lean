import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.RamerStep8a

                                                                                                           
                                                                                                                        
                                                                                
                                                                                                                   
                                                                                                              
                                                                                           
                                                                                                               
                                                                                        
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

section FiniteProjectedIdentity
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "Smap" => TM c s hs

theorem step8a
    (L : E → H) (ε : ℝ) (hL : Step8Hyp c s hs L ε) (N : ℕ) :
    finiteLevelLocalJacobi c s ε
      (Smap (projField c s N L))
      (NlsGge.Ramer.ramerJn c s N hs L) := by
  unfold finiteLevelLocalJacobi
  intro F hF
  exact NlsGge.Ramer.step8a c s N hs L hL F hF

end FiniteProjectedIdentity

end
end NlsGge.ThirdConsultation.R
