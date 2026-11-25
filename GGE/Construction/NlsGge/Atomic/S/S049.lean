import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Spectral.ReservedEnergyCoercivity38V1
import NlsGge.Spectral.PlaneMomentInequality38V1
import NlsGge.Hierarchy.FullEnergySpectralIdentification38
import NlsGge.Weights.Entire

                                                                                                                                                                                                                                                      
                                                                                                                     
                                                                                                            
                                                                                                             
                                                                                                                 
                                                                                                                 
                                                                                      
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open Matrix
open scoped BigOperators Topology ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.S

theorem reservedEnergy_ge_weight_Q2 {lo up : ℝ} (c : BoundedCoefficients lo up)
    (N : ℕ) (z : FourierPlane N) :
    NlsGge.Weights.weight c.val (Q2At N z ^ (1 / 4 : ℝ)) -
        NlsGge.coefficient c.val 0 - NlsGge.coefficient c.val 1 * Real.sqrt (Q2At N z) ≤
      reservedEnergy38 c N z := by
  have hQ0 : 0 ≤ Q2At N z := localCharge38_plane_nonneg N z 1
  have hr2 : (Q2At N z ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (Q2At N z) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hQ0]
    norm_num
  have hterm : ∀ j : ℕ, NlsGge.weightTerm c.val (Q2At N z ^ (1 / 4 : ℝ)) j =
      NlsGge.coefficient c.val j * Real.sqrt (Q2At N z) ^ j := by
    intro j
    unfold NlsGge.weightTerm
    rw [pow_mul, hr2]
  have hsa : Summable (fun j : ℕ => NlsGge.coefficient c.val j * Real.sqrt (Q2At N z) ^ j) :=
    (NlsGge.Weights.weightTerm_summable lo up c.val c.property.1
      (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2)
      (Q2At N z ^ (1 / 4 : ℝ))).congr hterm
  have hW : NlsGge.Weights.weight c.val (Q2At N z ^ (1 / 4 : ℝ)) =
      ∑' j : ℕ, NlsGge.coefficient c.val j * Real.sqrt (Q2At N z) ^ j := by
    unfold NlsGge.Weights.weight
    exact tsum_congr hterm
  have hsa1 : Summable (fun j : ℕ => NlsGge.coefficient c.val (j + 1) * Real.sqrt (Q2At N z) ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr hsa
  have hsa2 : Summable (fun j : ℕ =>
      NlsGge.coefficient c.val (j + 1 + 1) * Real.sqrt (Q2At N z) ^ (j + 1 + 1)) :=
    (summable_nat_add_iff 1).mpr hsa1
  have e1 : ∑' j : ℕ, NlsGge.coefficient c.val j * Real.sqrt (Q2At N z) ^ j =
      NlsGge.coefficient c.val 0 * Real.sqrt (Q2At N z) ^ 0 +
        ∑' j : ℕ, NlsGge.coefficient c.val (j + 1) * Real.sqrt (Q2At N z) ^ (j + 1) :=
    hsa.tsum_eq_zero_add
  have e2 : ∑' j : ℕ, NlsGge.coefficient c.val (j + 1) * Real.sqrt (Q2At N z) ^ (j + 1) =
      NlsGge.coefficient c.val 1 * Real.sqrt (Q2At N z) ^ 1 +
        ∑' j : ℕ, NlsGge.coefficient c.val (j + 1 + 1) * Real.sqrt (Q2At N z) ^ (j + 1 + 1) :=
    hsa1.tsum_eq_zero_add
  have h0 : NlsGge.coefficient c.val 0 * Real.sqrt (Q2At N z) ^ 0 = NlsGge.coefficient c.val 0 := by
    simp
  have h1 : NlsGge.coefficient c.val 1 * Real.sqrt (Q2At N z) ^ 1 =
      NlsGge.coefficient c.val 1 * Real.sqrt (Q2At N z) := by
    simp
  have hT : ∑' j : ℕ, NlsGge.coefficient c.val (j + 1 + 1) * Real.sqrt (Q2At N z) ^ (j + 1 + 1) ≤
      ∑' j : ℕ, NlsGge.coefficient c.val (j + 1 + 1) * localCharge38 (planeReal N z) (j + 1) := by
    refine Summable.tsum_le_tsum (fun k => ?_) hsa2 ?_
    · have hm := planeMoment_sqrt38 N z (k + 1) (by omega)
      exact mul_le_mul_of_nonneg_left hm (coefficient_nonneg38 c _)
    · exact (summable_nat_add_iff (f := fun j : ℕ => NlsGge.coefficient c.val (j + 1) * localCharge38 (planeReal N z) j) 1).mpr (reservedEnergy38_summable c N z)
  have hE : ∑' j : ℕ, NlsGge.coefficient c.val (j + 1) * localCharge38 (planeReal N z) j =
      NlsGge.coefficient c.val (0 + 1) * localCharge38 (planeReal N z) 0 +
        ∑' j : ℕ, NlsGge.coefficient c.val (j + 1 + 1) * localCharge38 (planeReal N z) (j + 1) :=
    (reservedEnergy38_summable c N z).tsum_eq_zero_add
  have hf0 : 0 ≤ NlsGge.coefficient c.val (0 + 1) * localCharge38 (planeReal N z) 0 :=
    mul_nonneg (coefficient_nonneg38 c _) (localCharge38_plane_nonneg N z 0)
  unfold reservedEnergy38
  linarith [hW, e1, e2, h0, h1, hT, hE, hf0]

end NlsGge.ThirdConsultation.S
