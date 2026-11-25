import Mathlib
import NlsGge.Birkhoff.W12Tilt38g
import NlsGge.ThirdConsultation.Common.FiniteSupport

                                                                                         
                                                                                  
                                                                                          
                                                                                                              
                                                                                                                     
                                                                                                                    
                                                                                                            
                                                                                                                   
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.T
noncomputable section

def lowerEnergyGapTerms {lo up : ℝ}
    (c : BoundedCoefficients lo up) (u : PhysicalL2) (n : ℤ) : ℝ :=
  gapIntegral38 (bCoef38 c.val) u n

def convergentWeightedFields {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (u : ℕ → ECarrier38 c s) : Prop :=
  ∃ v, Tendsto u atTop (𝓝 v)

def physicalInclusion {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) : ECarrier38 c s → PhysicalL2 :=
  physOfE38 c s

def UniformVanishingTails (a : ℕ → ℤ → ℝ) : Prop :=
  (∀ N : ℕ, Summable (a N)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ N : ℕ,
      |∑' n : ℤ, if K < n.natAbs then a N n else 0| ≤ ε

end
end NlsGge.ThirdConsultation.T
