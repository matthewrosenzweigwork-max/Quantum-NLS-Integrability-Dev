import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

                                                                                                  
                                                                                                                    
                                                                                           
                                                                                                                   
                                       
                                                                                                                 
                                                                                                                     
                                                                                         
                                                                                                                  
                                                                                                         
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r125_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (x : ECarrier38 c s) :
    ∃ e : ECarrier38 c s ≃L[ℝ] ECarrier38 c s,
      (e : ECarrier38 c s →L[ℝ] ECarrier38 c s) = 1 + fderiv ℝ ((B).KE38 O c s) x :=
  (B).exists_equiv_DT38 O c s x

end NlsGge.ThirdConsultation.R
