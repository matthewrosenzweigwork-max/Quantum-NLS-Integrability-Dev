import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W07Probability38b
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

theorem r112_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs' : s < 3 / 4) (hs1 : s ≤ 1) (N : ℕ) (x : FullWeightedHilbert c s) :
    fN38 c s N x =
      Real.exp (-(remainder38 c.val (physOfE38 c s (projE38 c s N x)))) *
        Real.exp (-(‖(B).yN38 O c hs1 N x -
          ((cmTrunc c N ((B).yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 / 2)) *
        Real.exp (-(‖(headPt c N (coordE c s x) : ActualCM c) +
          ((cmTrunc c N ((B).yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 -
            ‖(headPt c N (coordE c s x) : ActualCM c)‖ ^ 2) / 2) :=
  BirkhoffInput38.fN38_decomp B O c hs' hs1 N x

end NlsGge.ThirdConsultation.R
