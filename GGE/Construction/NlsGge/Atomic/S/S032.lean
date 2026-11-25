import Mathlib
import NlsGge.Atomic.S.S061
import NlsGge.Schur.ActualSchurOwnModeDerivative38V1

                                                                                                          
                                                                             
                                                                                                                
                                                                                                                
                                                                                                 
                                                                                                             
                                                                                                               
                                                                                                             
                                                                                                       
                                                                                                        
                                                                          
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

set_option backward.isDefEq.respectTransparency false in
/-- **S-032, real-form Wirtinger own-mode derivative** (Pro round 6 head, verbatim). -/
theorem schurQ_ownMode_wirtinger :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (n : ℤ),
      K * R ^ 3 ≤ |(n : ℝ)| → ∀ (w : SchurH1), ‖w‖ ≤ R →
      ‖ownWirtinger (realQAt (2 * R) n) n w - 1‖ ≤ C * R ^ 4 / |(n : ℝ)| ^ 2 := by
  have hI : 0 < freeResolventComplementaryInverseUniformConstant22 :=
    freeResolventComplementaryInverseUniformConstant22_posV2_31
  have hS : 0 < freeResolventSchurUniformConstant := by
    unfold freeResolventSchurUniformConstant
    positivity
  refine ⟨32 * (freeResolventComplementaryInverseUniformConstant22 ^ 2 *
      freeResolventSchurUniformConstant ^ 2),
    8 * max actualSchurCenterThresholdConstant38 1,
    mul_pos (by norm_num) (mul_pos (pow_pos hI 2) (pow_pos hS 2)),
    mul_pos (by norm_num) (lt_of_lt_of_le one_pos (le_max_right _ _)), ?_⟩
  intro R hR n hK w hw
  have hR2 : (1 : ℝ) ≤ 2 * R := by linarith
  -- the production threshold at radius 2R, from the single numerical threshold K
  have hthr : actualSchurCenterThresholdConstant38 * (2 * R) ^ 3 ≤ |(n : ℝ)| := by
    have h1 : actualSchurCenterThresholdConstant38 ≤ max actualSchurCenterThresholdConstant38 1 :=
      le_max_left _ _
    have h3 : 0 ≤ R ^ 3 := by positivity
    have h4 := mul_le_mul_of_nonneg_right h1 h3
    have h5 : actualSchurCenterThresholdConstant38 * (2 * R) ^ 3 =
        8 * (actualSchurCenterThresholdConstant38 * R ^ 3) := by ring
    linarith
  have hwlt : ‖w‖ < 2 * R := by linarith
  have hconj : ‖actualH1Conj38 w‖ = ‖w‖ := actualH1Conj38_norm w
  -- (a) differentiability of the real remainder q_n(v, v̄) - v_n at w (totalization before any fderiv identity)
  have hD : DifferentiableAt ℝ (actualSchurQnRealRemainder38 (2 * R) n) w :=
    actualSchurQnRealRemainder38_differentiableAt (2 * R) hR2 n hthr w hwlt
  -- (b) the n-th coordinate is a real-linear CLM with the restriction of actualH1CoordinateCLM38
  have hcoord : HasFDerivAt (fun v : SchurH1 => v n)
      ((actualH1CoordinateCLM38 n).restrictScalars ℝ) w := by
    refine ((actualH1CoordinateCLM38 n).restrictScalars ℝ).hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun v => ?_)
    simp only [ContinuousLinearMap.coe_restrictScalars', actualH1CoordinateCLM38_apply]
  -- (c) realQAt (2R) n = remainder + n-th coordinate, pointwise
  have hF : realQAt (2 * R) n = fun v : SchurH1 =>
      actualSchurQnRealRemainder38 (2 * R) n v + v n := by
    funext v
    simp only [realQAt, qAt, schurRealPair, actualSchurQnRealRemainder38, sub_add_cancel]
  have hFd : HasFDerivAt (realQAt (2 * R) n)
      (fderiv ℝ (actualSchurQnRealRemainder38 (2 * R) n) w +
        (actualH1CoordinateCLM38 n).restrictScalars ℝ) w := by
    rw [hF]
    exact hD.hasFDerivAt.add hcoord
  have hdF : fderiv ℝ (realQAt (2 * R) n) w =
      fderiv ℝ (actualSchurQnRealRemainder38 (2 * R) n) w +
        (actualH1CoordinateCLM38 n).restrictScalars ℝ := hFd.fderiv
  -- (d) the coordinate has Wirtinger value 1: its values on δ_n and i δ_n are 1 and i
  have hcn : (actualH1ModeVector38 n) n = 1 := by
    rw [actualH1ModeVector38_apply]; simp
  have hcoordE : (actualH1CoordinateCLM38 n).restrictScalars ℝ (actualH1ModeVector38 n) = 1 := by
    simp only [ContinuousLinearMap.coe_restrictScalars', actualH1CoordinateCLM38_apply, hcn]
  have hcoordIE : (actualH1CoordinateCLM38 n).restrictScalars ℝ
      (Complex.I • actualH1ModeVector38 n) = Complex.I := by
    simp only [ContinuousLinearMap.coe_restrictScalars', actualH1CoordinateCLM38_apply]
    show Complex.I * (actualH1ModeVector38 n) n = Complex.I
    rw [hcn, mul_one]
  -- (e) Wirtinger value of realQAt = Wirtinger value of the remainder + 1
  have hWirt : ownWirtinger (realQAt (2 * R) n) n w - 1 =
      (1 / 2 : ℂ) * (fderiv ℝ (actualSchurQnRealRemainder38 (2 * R) n) w (actualH1ModeVector38 n) -
        Complex.I * fderiv ℝ (actualSchurQnRealRemainder38 (2 * R) n) w
          (Complex.I • actualH1ModeVector38 n)) := by
    unfold ownWirtinger
    rw [hdF, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, hcoordE, hcoordIE]
    linear_combination (-(1 / 2 : ℂ)) * Complex.I_mul_I
  -- (f) the real-form Wirtinger dictionary S-061 at base point w, direction δ_n
  have hp2 : ‖actualH1Conj38 w‖ < 2 * R := by rw [hconj]; exact hwlt
  have hQ : DifferentiableAt ℂ (qAt (2 * R) n) (schurRealPair w) :=
    actualSchurQn38_differentiableAt (2 * R) hR2 n hthr (schurRealPair w) hwlt hp2
  have hS61 := realType_wirtinger_first_component (qAt (2 * R) n) n w (actualH1ModeVector38 n) hQ
  have hS61' : (1 / 2 : ℂ) * (fderiv ℝ (actualSchurQnRealRemainder38 (2 * R) n) w
        (actualH1ModeVector38 n) -
      Complex.I * fderiv ℝ (actualSchurQnRealRemainder38 (2 * R) n) w
        (Complex.I • actualH1ModeVector38 n)) =
      fderiv ℂ (qAt (2 * R) n) (schurRealPair w) (actualH1ModeVector38 n, 0) -
        (actualH1ModeVector38 n) n := hS61
  have hmain : ownWirtinger (realQAt (2 * R) n) n w - 1 =
      fderiv ℂ (qAt (2 * R) n) (schurRealPair w) (actualH1ModeVector38 n, 0) - 1 := by
    rw [hWirt, hS61', hcn]
  -- (g) complex own-mode bound (production), at the real point (w, w̄) with ‖w‖ ≤ R
  have hp2' : ‖actualH1Conj38 w‖ ≤ R := by rw [hconj]; exact hw
  have hbound : ‖fderiv ℂ (qAt (2 * R) n) (schurRealPair w) (actualH1ModeVector38 n, 0) - 1‖ ≤
      2 * actualSchurOwnModeScale38 (2 * R) n :=
    actualSchurQn38_ownMode_derivative R hR n hthr (schurRealPair w) hw hp2'
  rw [hmain]
  calc ‖fderiv ℂ (qAt (2 * R) n) (schurRealPair w) (actualH1ModeVector38 n, 0) - 1‖
      ≤ 2 * actualSchurOwnModeScale38 (2 * R) n := hbound
    _ = 32 * (freeResolventComplementaryInverseUniformConstant22 ^ 2 *
          freeResolventSchurUniformConstant ^ 2) * R ^ 4 / |(n : ℝ)| ^ 2 := by
      unfold actualSchurOwnModeScale38
      ring

end NlsGge.ThirdConsultation.S
end
