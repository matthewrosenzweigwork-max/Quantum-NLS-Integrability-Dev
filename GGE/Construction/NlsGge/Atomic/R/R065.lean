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

theorem r065_main (x : H1_38) (N : ℕ) :
    LinearMap.adjoint ((B).LNmap x N) * (cp38 N).JV * (B).LNmap x N =
      (cp38 N).JV - (cp38 N).resRange ((cp38 N).Qop ((B).LxN x N)) ((cp38 N).Qop_mem ((B).LxN x N)) :=
  NlsGge.Birkhoff.BirkhoffInput38.F01_04_operator B x N

end NlsGge.ThirdConsultation.R
