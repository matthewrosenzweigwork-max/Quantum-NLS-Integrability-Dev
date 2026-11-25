import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Hierarchy.UniformPartitionBoundAux38

                                                                                                           
                                                                                                                     
                                                                                                        
                                                                                                         
                                                                                                             
                                                                                          
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open Matrix
open scoped BigOperators Topology ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.S

theorem reservedWeight_coefficients {lo up : ℝ} (c : BoundedCoefficients lo up) :
    0 < shiftEps38 lo up ∧ shiftEps38 lo up ≤ (1 / 4 : ℝ) ∧
      ∀ j : ℕ, 3 * lo / 4 ≤ c.val j - shiftEps38 lo up * c.val (j + 1) / ((j : ℝ) + 1) ^ 4 ∧
        c.val j - shiftEps38 lo up * c.val (j + 1) / ((j : ℝ) + 1) ^ 4 ≤ up := by
  have hl : 0 < lo := c.property.1
  have hlu : lo ≤ up := c.property.2.1
  refine ⟨shiftEps38_pos hl hlu, shiftEps38_le hl hlu, fun j => ?_⟩
  exact (shiftedSeq38_admitted c).2.2 j

end NlsGge.ThirdConsultation.S
