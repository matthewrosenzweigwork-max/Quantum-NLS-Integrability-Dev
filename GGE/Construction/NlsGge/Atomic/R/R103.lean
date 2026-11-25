import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.ThirdConsultation.R.R103Core

                                                                                                                      
                                                                                                                            
                                                                                                                  
                                                                                                             
                                                                                                                       
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem remainder_tail_uniform_on_convergent {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (hs : s < 3 / 4)
    (x : ℕ → ECarrier38 c s) (xInf : ECarrier38 c s)
    (hx : Tendsto x atTop (𝓝 xInf)) :
    (∀ j : ℕ, Summable (fun n : ℤ =>
      remainderSummand38 c.val (physOfE38 c s (x j)) n)) ∧
    (∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if N < n.natAbs then
        |remainderSummand38 c.val (physOfE38 c s (x j)) n| else 0) < eps) :=
  NlsGge.Birkhoff.R103Aux.tail_uniform_of B O c s hs x xInf hx

end NlsGge.ThirdConsultation.R
