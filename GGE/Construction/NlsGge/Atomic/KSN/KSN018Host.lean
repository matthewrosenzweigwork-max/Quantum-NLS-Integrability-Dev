import Mathlib
import NlsGge.Atomic.KSN.KSN012Host

                                                                                                                             
                                                                                                                           
                                                                                                                            
                                                                                                        
                                                     
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

def smoothingCoefficient (N : ℕ) (x : PairScale (N : ℝ)) (b : Bool) (n : ℤ) : ℂ :=
  scalarBirkhoff b n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) +
    rawCoefficient (N : ℝ) x b (if b then -n else n)

def complexSmoothing (N : ℕ) (x : PairScale (N : ℝ)) : PairScale ((N : ℝ) + 1) :=
  sequenceLift ((N : ℝ) + 1) (smoothingCoefficient N x)

end
end NlsGge.ThirdConsultation.KSN
