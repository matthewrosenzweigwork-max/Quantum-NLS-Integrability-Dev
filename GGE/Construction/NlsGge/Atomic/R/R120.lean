import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.ThirdConsultation.R.R120Tail

                                                                                                                      
                                                                                                                   
                                                                                                                           
                                                                                                                          
                                                                                                                         
                                                                                                                  
                                                                                                             
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem projected_collision_tail (N : ℕ) (x y : H1_38)
    (hx : projC38 ((1 : ℕ) : ℝ) N x = x)
    (hy : projC38 ((1 : ℕ) : ℝ) N y = y)
    (hcol : projC38 ((1 : ℕ) : ℝ) N ((B).TC 1 x) =
      projC38 ((1 : ℕ) : ℝ) N ((B).TC 1 y)) :
    ‖(B).TC 1 x - (B).TC 1 y‖ ≤
      (japaneseBracket ((N + 1 : ℕ) : ℤ))⁻¹ *
        ‖(B).Kfwd1 O x - (B).Kfwd1 O y‖ :=
  NlsGge.Birkhoff.R120Aux.projected_collision_tail_of B O N x y hx hy hcol

end NlsGge.ThirdConsultation.R
