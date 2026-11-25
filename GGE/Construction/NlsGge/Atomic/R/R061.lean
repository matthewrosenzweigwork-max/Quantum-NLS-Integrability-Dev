import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.F01Determinant38c
import NlsGge.Ramer.RamerFiniteChainRule

                                                                                                              
                                                                                                                  
                                                                                                   
                                                         
                                                                                                       
                                                              
                                                                                                             
                                                                                 
                                                                                                                
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r061_main (x1 ξ1 : H1_38) :
    (B).Bop (i10_38 x1) (i10_38 ξ1) = i20_38 ((B).Dfwd O x1 ξ1) :=
  NlsGge.Birkhoff.BirkhoffInput38.Bop_incl B O x1 ξ1

theorem r061_2 (x1 ξ1 : H1_38) :
    ContinuousLinearMap.adjoint ((B).Bop (i10_38 x1)) (i10_38 ξ1) = i20_38 ((B).Dadj O x1 ξ1) :=
  NlsGge.Birkhoff.BirkhoffInput38.Bop_adjoint_incl B O x1 ξ1

theorem r061_3 : Continuous ((B).Dfwd O) :=
  NlsGge.Birkhoff.BirkhoffInput38.continuous_Dfwd B O

theorem r061_4 : Continuous ((B).Dadj O) :=
  NlsGge.Birkhoff.BirkhoffInput38.continuous_Dadj B O

end NlsGge.ThirdConsultation.R
