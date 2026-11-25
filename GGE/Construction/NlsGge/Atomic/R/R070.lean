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

theorem r070_main {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (w : ι → ℝ) (hw : ∀ i : ι, w i ≠ 0) :
    Matrix.det (Matrix.diagonal w * M * Matrix.diagonal (fun i : ι => (w i)⁻¹)) =
      Matrix.det M := by
  have hp : (∏ i : ι, w i) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hw i)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Finset.prod_inv_distrib]
  field_simp

end NlsGge.ThirdConsultation.R
