import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.F01Determinant38d
import NlsGge.Ramer.RamerFiniteChainRule

                                                                                                              
                                                                                                                 
                                                                                                              
                                                                                                                                   
                                                                                                 
                                                                                           
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r067_main (x : H1_38) (N : ℕ) :
    ‖(cp38 N).Mhs ((B).cHS O x N)‖ ≤ ‖(B).cHS O x N‖ ^ 2 ∧
      |LinearMap.trace ℝ (cp38 N).V ((B).MNmap x N)| ≤ ‖(B).cHS O x N‖ ^ 2 :=
  NlsGge.Birkhoff.BirkhoffInput38.F01_05_quadratic B O x N

end NlsGge.ThirdConsultation.R
