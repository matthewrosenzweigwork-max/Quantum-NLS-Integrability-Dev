import Mathlib
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Schur.ActualSchurBallMap38V1

                                                                                                 
                                                                                  
                                                                                                        
                                                                                            
                                                                   
                                                                                                      

set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.M049Aux

theorem incl_norm_le {r s : ℝ} (h : r ≤ s) (x : SobolevCarrier38 s) : ‖carrierIncl38 h x‖ ≤ ‖x‖ := by
  have h1 := carrier_hasSum_norm_sq38 r (carrierIncl38 h x)
  have h2 := carrier_hasSum_norm_sq38 s x
  rw [carrierCoe38_incl38] at h1
  have hle : ‖carrierIncl38 h x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    hasSum_le (fun n => mul_le_mul_of_nonneg_right
      (by simpa using sobolevModeWeight_mono_one h n) (sq_nonneg _)) h1 h2
  have h5 := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h5

theorem weighted_le_norm (s : ℝ) (z : SobolevCarrier38 s) (wt : ℤ → ℝ) (K : ℝ)
    (hwn : ∀ n, 0 ≤ wt n) (hw : ∀ n, wt n ≤ K * sobolevModeWeight s n) :
    Summable (fun n : ℤ => wt n * ‖carrierCoe38 s z n‖ ^ 2) ∧
      (∑' n : ℤ, wt n * ‖carrierCoe38 s z n‖ ^ 2) ≤ K * ‖z‖ ^ 2 := by
  have h := carrier_hasSum_norm_sq38 s z
  have hle : ∀ n, wt n * ‖carrierCoe38 s z n‖ ^ 2 ≤
      K * (sobolevModeWeight s n * ‖carrierCoe38 s z n‖ ^ 2) := fun n => by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hw n) (sq_nonneg _)
  have hs : Summable (fun n : ℤ => wt n * ‖carrierCoe38 s z n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hwn n) (sq_nonneg _)) hle (h.summable.mul_left K)
  refine ⟨hs, ?_⟩
  calc (∑' n : ℤ, wt n * ‖carrierCoe38 s z n‖ ^ 2)
      ≤ ∑' n : ℤ, K * (sobolevModeWeight s n * ‖carrierCoe38 s z n‖ ^ 2) :=
        hs.tsum_le_tsum hle (h.summable.mul_left K)
    _ = K * ‖z‖ ^ 2 := by rw [tsum_mul_left, h.tsum_eq]

theorem weighted_le_incl {r s : ℝ} (hrs : r ≤ s) (z : SobolevCarrier38 s) (wt : ℤ → ℝ) (K : ℝ)
    (hwn : ∀ n, 0 ≤ wt n) (hw : ∀ n, wt n ≤ K * sobolevModeWeight r n) :
    Summable (fun n : ℤ => wt n * ‖carrierCoe38 s z n‖ ^ 2) ∧
      (∑' n : ℤ, wt n * ‖carrierCoe38 s z n‖ ^ 2) ≤ K * ‖carrierIncl38 hrs z‖ ^ 2 := by
  have h := weighted_le_norm r (carrierIncl38 hrs z) wt K hwn hw
  rw [carrierCoe38_incl38] at h
  exact h

theorem base_weight_le (n : ℤ) :
    (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 ≤ (1 + 2 * Real.pi) ^ 2 * (1 + (n : ℝ) ^ 2) := by
  have ht : |2 * Real.pi * (n : ℝ)| = 2 * Real.pi * |(n : ℝ)| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [ht]
  have hn2 : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
  rw [hn2]
  have hpi := Real.pi_pos
  have t0 := abs_nonneg (n : ℝ)
  nlinarith [sq_nonneg (|(n : ℝ)| - 1), mul_nonneg hpi.le (sq_nonneg (|(n : ℝ)| - 1)),
    mul_nonneg hpi.le t0, mul_nonneg (mul_nonneg hpi.le hpi.le) (sq_nonneg (|(n : ℝ)|))]

theorem sobolevModeWeight_nat (r : ℕ) (n : ℤ) :
    sobolevModeWeight (r : ℝ) n = (1 + (n : ℝ) ^ 2) ^ r := by
  unfold sobolevModeWeight japaneseBracket
  rw [show (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ) by push_cast; ring]
  change Real.sqrt (1 + (n : ℝ) ^ 2) ^ (((2 * r : ℕ)) : ℝ) = _
  rw [Real.rpow_natCast, pow_mul, Real.sq_sqrt (by positivity)]

theorem molnar_weight_le_nat (r : ℕ) (n : ℤ) :
    ((1 + |2 * Real.pi * (n : ℝ)|) ^ r) ^ 2 ≤ (1 + 2 * Real.pi) ^ (2 * r) * sobolevModeWeight (r : ℝ) n := by
  rw [sobolevModeWeight_nat, ← pow_mul, mul_comm r 2, pow_mul, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (base_weight_le n) r

theorem molnar_weight_le_one (n : ℤ) :
    ((1 + |2 * Real.pi * (n : ℝ)|) ^ 1) ^ 2 ≤ (1 + 2 * Real.pi) ^ 2 * sobolevModeWeight 1 n := by
  rw [NlsGge.Schur.sobolevModeWeight_one38, pow_one]
  exact base_weight_le n

theorem molnar_weight_le_zero (n : ℤ) :
    ((1 + |2 * Real.pi * (n : ℝ)|) ^ 0) ^ 2 ≤ 1 * sobolevModeWeight 0 n := by
  unfold sobolevModeWeight
  simp

end NlsGge.ThirdConsultation.M049Aux
