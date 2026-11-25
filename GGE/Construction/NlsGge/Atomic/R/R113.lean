import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.Birkhoff.W10Localized38e

                                                                                                  
                                                                                                                       
                                                                                                                   
                                                                                                                 
                                                                               
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r113_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (yN : ℕ → ActualCM c) (Kinf : ActualCM c)
    (h1 : Tendsto yN atTop (𝓝 Kinf)) :
    Tendsto (fun N : ℕ => ‖yN N - ((cmTrunc c N (yN N) : actualCMHead c N) : ActualCM c)‖ ^ 2 / 2)
      atTop (𝓝 0) :=
  tendsto_tail_of_tendsto38 c yN Kinf h1

end NlsGge.ThirdConsultation.R
