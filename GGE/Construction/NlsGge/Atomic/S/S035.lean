import Mathlib
import NlsGge.Atomic.S.S037
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                            
                                                                                                                  
                                                                   
                                                                                                                       
                                                                                                                   
                                                                                                           
                                                                                      
                                                                                              
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem schurBall_derivative_hs (M N : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : schurAllThreshold * R ^ 6 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : z ∈ schurH1Ball N R) :
    matrixHSNorm (actualSchurBallMapH1Matrix38 N M z) ^ 2 ≤
      actualSchurBallHSConstant38 * R ^ 6 / (M : ℝ) := by
  have hz' : ‖planeH1Embedding38 N z‖ < R := hz
  have hR3 : 0 ≤ R ^ 3 := by positivity
  have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR
  have h36 : R ^ 3 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
  have hK := abs_nonneg actualSchurCenterThresholdConstant38
  have hA : 512 * (1 + |actualSchurCenterThresholdConstant38|) ≤ schurAllThreshold := by
    unfold schurAllThreshold
    have := abs_nonneg schurCommonThreshold
    have := abs_nonneg actualSchurShiftedRootsConstant38
    have := abs_nonneg actualSchurGapLocalConstant38
    have := abs_nonneg (freeResolventComplementaryInverseUniformConstant22 ^ 2 *
      freeResolventSchurUniformConstant ^ 2)
    linarith
  have hApos : 0 ≤ schurAllThreshold := by linarith
  -- 1 ≤ M
  have hM1 : 1 ≤ M := by
    have h512 : (512 : ℝ) ≤ schurAllThreshold := by linarith
    have h1 : (1 : ℝ) ≤ schurAllThreshold * R ^ 6 := by
      have := mul_le_mul h512 hR6 zero_le_one hApos
      linarith
    exact_mod_cast h1.trans hM
  -- the production center threshold at radius 4R
  have hMc : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ) := by
    have e : (4 * R) ^ 3 = 64 * R ^ 3 := by ring
    rw [e]
    have h1 : actualSchurCenterThresholdConstant38 * (64 * R ^ 3) ≤
        64 * |actualSchurCenterThresholdConstant38| * R ^ 3 := by
      nlinarith [le_abs_self actualSchurCenterThresholdConstant38]
    have h2 : 64 * |actualSchurCenterThresholdConstant38| * R ^ 3 ≤
        64 * |actualSchurCenterThresholdConstant38| * R ^ 6 :=
      mul_le_mul_of_nonneg_left h36 (by positivity)
    have h3 : 64 * |actualSchurCenterThresholdConstant38| * R ^ 6 ≤ schurAllThreshold * R ^ 6 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hS := actualSchurBallMap38_hs_le N M hM1 R hR hMc z hz'
  unfold matrixHSNorm
  exact (Real.sq_sqrt
    (Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun c _ => sq_nonneg _)).le.trans hS

end NlsGge.ThirdConsultation.S

end
