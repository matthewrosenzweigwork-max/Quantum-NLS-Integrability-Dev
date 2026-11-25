import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52

                                                                                                                        
                                                                                                    
                                                                                                                      
                                                                                                                 
                                                                                                                        
                 
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators RealInnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.R
noncomputable section

def L1Converges {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ) : Prop :=
  Tendsto (fun N => eLpNorm (fun x => f N x-g x) 1 μ) atTop (𝓝 0)

end
end NlsGge.ThirdConsultation.R
