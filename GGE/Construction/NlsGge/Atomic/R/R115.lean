import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.ThirdConsultation.R.R110Host
import NlsGge.ThirdConsultation.R.R109Host
import NlsGge.Birkhoff.W07Probability38e
import NlsGge.Ramer.RamerFiniteChainRule

                                                                                                              
                                                                                                                 
                                                                       
                                                                                                                        
                                                                                                   
                                                                                                                   
                                                                                                            
                                                                       
                                                                                                                       
                                                                            
                                                                                  
                                                                                                        
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem actual_fN_tendstoInMeasure {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    let hs1 : s ≤ 1 := by linarith
    Integrable (actualRamerDensity c s hs hs1) (fullWeightedSequenceGaussian c s) ∧
    (∫ x : ECarrier38 c s, actualRamerDensity c s hs hs1 x
      ∂(fullWeightedSequenceGaussian c s)) = (B).ZW38 c.val ∧
    TendstoInMeasure (fullWeightedSequenceGaussian c s)
      (fun N : ℕ => fN38 c s N) atTop (actualRamerDensity c s hs hs1) := by
  intro hs1
  obtain ⟨δK, hδ, -, hInt, hZ, hT, -⟩ := NlsGge.Birkhoff.W07_38 B O c s hs hs'
  have hae : fW06_38 c s hs ((B).KW06_38 O c hs1) δK =ᵐ[fullWeightedSequenceGaussian c s]
      actualRamerDensity c s hs hs1 :=
    NlsGge.Birkhoff.fW06_ae_unique_W07 c s B O hs hs1 δK (canonicalDelta c s hs hs1) hδ
      (canonicalDelta_spec c s hs hs1)
  refine ⟨hInt.congr hae, ?_, hT.congr_right hae⟩
  exact (integral_congr_ae hae).symm.trans hZ

end NlsGge.ThirdConsultation.R
