import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W11Equivalence38c
import NlsGge.Birkhoff.W10Localized38i
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.ThirdConsultation.R.R142Host

                                                                                                  
                                                                                                                    
                                                                                                                        
                                                                                                                      
                                                                                                                    
                                                                                                               
                                                                                                                     
                                                                                                                       
                                                                                                               
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r142_main {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ)
    (f : FullWeightedHilbert c s → ℝ) (hs : (1 : ℝ) / 2 < s)
    (hW : W11Weight38 B c s f) :
    L1Converges (fullWeightedSequenceGaussian c s) (fun N : ℕ => fN38 c s N) f ↔
      UniformIntegrable (fun N : ℕ => fN38 c s N) 1 (fullWeightedSequenceGaussian c s) :=
  (NlsGge.Birkhoff.tendsto_l1_iff_eLpNorm_W11 (μ := fullWeightedSequenceGaussian c s)
      (fn := fun N x => fN38 c s N x) (f := f) (fun N => BirkhoffInput38.integrable_fN38 c hs N) hW.integrable).symm.trans
    ((B).l1_iff_uniformIntegrable_W11' c hs hW)

end NlsGge.ThirdConsultation.R
