import Mathlib
import NlsGge.Atomic.KSN.KSN012Sup3
import NlsGge.ThirdConsultation.KSPS.KSPS019Host
import NlsGge.ThirdConsultation.KSPS.KSPS003Host

                                                                                                                             
                                                                                                                        
                                                                                                                          
                                                                                                                            
                                                                     
                                                                                                       
                                                                                                           
                                                                          
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem sup5_bracket_sq_le (n : ℤ) :
    bracket n ^ 2 ≤ NlsGge.ThirdConsultation.KSPS.indexWeight n ^ 2 := by
  unfold bracket NlsGge.ThirdConsultation.KSPS.indexWeight
  rw [Real.sq_sqrt (by positivity)]
  have hab : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hab]
  have hsq : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
  rcases le_total 1 |(n : ℝ)| with h | h
  · rw [max_eq_right h, hsq]; linarith
  · rw [max_eq_left h]; nlinarith [sq_nonneg (n : ℝ)]

theorem KSN012Sup5_missingB_of_missingA
    (hA : ∀ B : ℝ, 0 < B → ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1, NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 φ ≤ B →
        (∑' n : ℤ, if N ≤ n.natAbs then
          ENNReal.ofReal (NlsGge.ThirdConsultation.KSPS.indexWeight n ^ 2 *
            ‖NlsGge.ThirdConsultation.KSPS.mu φ n - NlsGge.ThirdConsultation.KSPS.criticalEigenvalue φ n‖ ^ 2)
          else 0) ≤ ENNReal.ofReal C) :
    ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : PairScale 1, ‖x‖ ≤ B →
        (∑' n : ℤ, if N ≤ n.natAbs then
          ENNReal.ofReal (bracket n ^ 2 *
            ‖muSeq (pairPotential 1 (by norm_num) x) n - lamDot (pairPotential 1 (by norm_num) x) n‖ ^ 2)
          else 0) ≤ ENNReal.ofReal C := by
  intro B hB
  obtain ⟨C, N, hC, h⟩ := hA (2 * B + 1) (by linarith)
  refine ⟨C, N, hC, fun x hx => ?_⟩
  have hφ : NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 (toSobolevC x) ≤ 2 * B + 1 := by
    have := sobolevNorm_toSobolevC_le x
    linarith
  refine le_trans (ENNReal.tsum_le_tsum (fun n => ?_)) (h (toSobolevC x) hφ)
  split_ifs with hn
  · rw [mu_toSobolevC, criticalEigenvalue_toSobolevC]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (sup5_bracket_sq_le n) (sq_nonneg _))
  · exact le_rfl

end
end NlsGge.ThirdConsultation.KSN
