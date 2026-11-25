import Mathlib
import NlsGge.GK38.Defs
import NlsGge.GK38.PairPotential

                                                                                                                
                                                                                                  
                                                                                                                                                 
                                                                                                                          
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Squared paired norm, not the house product's maximum norm. -/
def pairGradientNorm (v : PotPair) : ℝ := Real.sqrt (‖v.1‖^2 + ‖v.2‖^2)

def fourierMode (a : ℤ) (n : ℤ) : PotPair :=
  if a = 1 then (0, fourierLp (T := (1 : ℝ)) 2 (-n))
  else (fourierLp (T := (1 : ℝ)) 2 n, 0)

end
end NlsGge.GKDefinitionDesign
