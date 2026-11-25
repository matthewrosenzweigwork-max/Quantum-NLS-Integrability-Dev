import Mathlib
import NlsGge.Atomic.S.S061
import NlsGge.Atomic.S.S064
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                            
                                                                                                                  
                                                                   
                         
                                                                                                         
                                                                                         
                                                                                                                     
                                                                                                                   
                                                                                                                        
                                                                                                                      
                                                                                                                  
                                                                                                               
                                                
                                                                                                                     
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

set_option backward.isDefEq.respectTransparency false in
theorem schurBall_realTrace (M N : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : schurAllThreshold * R ^ 6 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : z ∈ schurH1Ball N R) :
    Matrix.trace (actualSchurBallMapH1Matrix38 N M z) =
      Matrix.trace (actualSchurBallMapPlainMatrix38 N M z) ∧
    Matrix.trace (actualSchurBallMapH1Matrix38 N M z) =
      2 * (∑ i : Fin (2 * N + 1),
        if (modeIndex N i).natAbs ≤ M then (0 : ℂ)
        else ownWirtinger (realQAt (4 * R) (modeIndex N i)) (modeIndex N i)
          (planeH1Embedding38 N z) - 1).re ∧
    |Matrix.trace (actualSchurBallMapH1Matrix38 N M z)| ≤
      actualSchurBallTraceConstant38 * R ^ 4 / (M : ℝ) := by
  have hz' : ‖planeH1Embedding38 N z‖ < R := hz
  have h4R : (1 : ℝ) ≤ 4 * R := by linarith
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
  have hM1 : 1 ≤ M := by
    have h512 : (512 : ℝ) ≤ schurAllThreshold := by linarith
    have h1 : (1 : ℝ) ≤ schurAllThreshold * R ^ 6 := by
      have := mul_le_mul h512 hR6 zero_le_one hApos
      linarith
    exact_mod_cast h1.trans hM
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
  -- (2') pointwise: the real-form Wirtinger own derivative of realQAt (4R) n minus 1 is the production entry
  have hW : ∀ (n : ℤ), actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ |(n : ℝ)| →
      ∀ (w : SchurH1), ‖w‖ < R →
      ownWirtinger (realQAt (4 * R) n) n w - 1 = actualSchurBallWirtinger38 R n w := by
    intro n hthr w hwR
    have hwlt : ‖w‖ < 4 * R := by linarith
    have hconj : ‖actualH1Conj38 w‖ = ‖w‖ := actualH1Conj38_norm w
    have hD : DifferentiableAt ℝ (actualSchurQnRealRemainder38 (4 * R) n) w :=
      actualSchurQnRealRemainder38_differentiableAt (4 * R) h4R n hthr w hwlt
    have hcoord : HasFDerivAt (fun v : SchurH1 => v n)
        ((actualH1CoordinateCLM38 n).restrictScalars ℝ) w := by
      refine ((actualH1CoordinateCLM38 n).restrictScalars ℝ).hasFDerivAt.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun v => ?_)
      simp only [ContinuousLinearMap.coe_restrictScalars', actualH1CoordinateCLM38_apply]
    have hF : realQAt (4 * R) n = fun v : SchurH1 =>
        actualSchurQnRealRemainder38 (4 * R) n v + v n := by
      funext v
      simp only [realQAt, qAt, schurRealPair, actualSchurQnRealRemainder38, sub_add_cancel]
    have hFd : HasFDerivAt (realQAt (4 * R) n)
        (fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) n) w +
          (actualH1CoordinateCLM38 n).restrictScalars ℝ) w := by
      rw [hF]
      exact hD.hasFDerivAt.add hcoord
    have hdF : fderiv ℝ (realQAt (4 * R) n) w =
        fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) n) w +
          (actualH1CoordinateCLM38 n).restrictScalars ℝ := hFd.fderiv
    have hcn : (actualH1ModeVector38 n) n = 1 := by
      rw [actualH1ModeVector38_apply]; simp
    have hcoordE : (actualH1CoordinateCLM38 n).restrictScalars ℝ (actualH1ModeVector38 n) = 1 := by
      simp only [ContinuousLinearMap.coe_restrictScalars', actualH1CoordinateCLM38_apply, hcn]
    have hcoordIE : (actualH1CoordinateCLM38 n).restrictScalars ℝ
        (Complex.I • actualH1ModeVector38 n) = Complex.I := by
      simp only [ContinuousLinearMap.coe_restrictScalars', actualH1CoordinateCLM38_apply]
      show Complex.I * (actualH1ModeVector38 n) n = Complex.I
      rw [hcn, mul_one]
    have hWirt : ownWirtinger (realQAt (4 * R) n) n w - 1 =
        (1 / 2 : ℂ) * (fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) n) w (actualH1ModeVector38 n) -
          Complex.I * fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) n) w
            (Complex.I • actualH1ModeVector38 n)) := by
      unfold ownWirtinger
      rw [hdF, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, hcoordE, hcoordIE]
      linear_combination (-(1 / 2 : ℂ)) * Complex.I_mul_I
    have hp2 : ‖actualH1Conj38 w‖ < 4 * R := by rw [hconj]; exact hwlt
    have hQ : DifferentiableAt ℂ (qAt (4 * R) n) (schurRealPair w) :=
      actualSchurQn38_differentiableAt (4 * R) h4R n hthr (schurRealPair w) hwlt hp2
    have hS61 := realType_wirtinger_first_component (qAt (4 * R) n) n w (actualH1ModeVector38 n) hQ
    have hS61' : (1 / 2 : ℂ) * (fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) n) w
          (actualH1ModeVector38 n) -
        Complex.I * fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) n) w
          (Complex.I • actualH1ModeVector38 n)) =
        fderiv ℂ (qAt (4 * R) n) (schurRealPair w) (actualH1ModeVector38 n, 0) -
          (actualH1ModeVector38 n) n := hS61
    rw [hWirt, hS61', hcn]
    rfl
  refine ⟨?_, ?_, actualSchurBallMap38_trace_le N M hM1 R hR hMc z hz'⟩
  · rw [actualSchurBallMapH1Matrix38_eq]
    exact (weighted_real_matrix_similarity (B := actualSchurBallMapPlainMatrix38 N M z)
      (fun c => planeH1Scale38_pos N c)).1
  · rw [actualSchurBallMap38_trace_eq N M R hR hMc z hz']
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : (modeIndex N i).natAbs ≤ M
    · simp only [hi, if_true]
    · simp only [hi, if_false]
      have hthr : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤
          |((modeIndex N i : ℤ) : ℝ)| := by
        have := natAbs_gt_abs38 M _ hi
        linarith
      exact (hW (modeIndex N i) hthr (planeH1Embedding38 N z) hz').symm

end NlsGge.ThirdConsultation.S

end
