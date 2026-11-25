import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.ThirdConsultation.R.R101Host

                                                                                                  
                                                                                                                  
                                                                                                                  
                                                                                                                        
                                                                                                                         
                                                                                                                
                                                                                                             
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem actualWeightedBirkhoffHomeo_apply {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (x : ECarrier38 c s) :
    eCoe38 c s (actualWeightedBirkhoffHomeo c s x) =
      (fun n : ℤ => NlsGge.GKDefinitionDesign.physicalBirkhoff (physFW06_38 c s x) n) := by
  show eCoe38 c s ((B).weightedHomeoE38 O c s x) = _
  rw [BirkhoffInput38.weightedHomeoE38_apply]
  show PDE.actualT38 (eCoe38 c s x) = _
  rw [← fourierSeq38_physOfE38 c s x, PDE.actualT38_fourierSeq38]
  rfl

theorem actualWeightedBirkhoffHomeo_symm_apply {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (x : ECarrier38 c s) :
    eCoe38 c s ((actualWeightedBirkhoffHomeo c s).symm x) =
      (B).Tinv (eCoe38 c s x) :=
  BirkhoffInput38.weightedHomeoE38_symm_apply B O c s x

end NlsGge.ThirdConsultation.R
