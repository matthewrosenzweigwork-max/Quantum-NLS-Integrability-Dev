import Mathlib
import NlsGge.Schur.ActualSchurQnRealDerivative38V1
import NlsGge.Schur.ActualSchurQnCauchy38V1
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                                                                                                           
                                                                                                                                                                                                 
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem schurQ_remainder_fderiv_bound :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (n : ℤ),
      K * R ^ 3 ≤ |(n : ℝ)| → ∀ (w : SchurH1), ‖w‖ ≤ R →
      ‖realQAt (4 * R) n w - w n‖ ≤ C * R ^ 4 / |(n : ℝ)| ^ 2 ∧
      ‖fderiv ℝ (qRemainderAt (4 * R) n) w‖ ≤ C * R ^ 3 / |(n : ℝ)| ^ 2 := by
  refine ⟨256 * (|actualSchurBremConstant38| + 1),
    64 * max actualSchurCenterThresholdConstant38 1,
    by positivity, mul_pos (by norm_num) (lt_of_lt_of_le one_pos (le_max_right _ _)), ?_⟩
  intro R hR n hK w hw
  have hR0 : (0 : ℝ) < R := by linarith
  have h4R : (1 : ℝ) ≤ 4 * R := by linarith
  have hKpos : (0 : ℝ) < 64 * max actualSchurCenterThresholdConstant38 1 :=
    mul_pos (by norm_num) (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hnpos : (0 : ℝ) < |(n : ℝ)| := lt_of_lt_of_le (mul_pos hKpos (pow_pos hR0 3)) hK
  have hn0 : |(n : ℝ)| ≠ 0 := hnpos.ne'
  have hRne : R ≠ 0 := hR0.ne'
  have hthr : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ |(n : ℝ)| := by
    have hc : actualSchurCenterThresholdConstant38 ≤ max actualSchurCenterThresholdConstant38 1 :=
      le_max_left _ _
    have hpos : (0 : ℝ) ≤ 64 * R ^ 3 := by positivity
    calc actualSchurCenterThresholdConstant38 * (4 * R) ^ 3
        = actualSchurCenterThresholdConstant38 * (64 * R ^ 3) := by ring
      _ ≤ max actualSchurCenterThresholdConstant38 1 * (64 * R ^ 3) :=
          mul_le_mul_of_nonneg_right hc hpos
      _ = 64 * max actualSchurCenterThresholdConstant38 1 * R ^ 3 := by ring
      _ ≤ |(n : ℝ)| := hK
  have hpair1 : ‖(schurRealPair w).1‖ ≤ 4 * R := by
    show ‖w‖ ≤ 4 * R
    linarith
  have hpair2 : ‖(schurRealPair w).2‖ ≤ 4 * R := by
    show ‖actualH1Conj38 w‖ ≤ 4 * R
    rw [actualH1Conj38_norm]
    linarith
  have hq := actualSchurQn38_sub_fourier_bound (4 * R) h4R n hthr (schurRealPair w) hpair1 hpair2
  have hd := actualSchurQnRealRemainder38_fderiv_norm_le R hR n hthr w hw
  have hB : actualSchurBremConstant38 ≤ |actualSchurBremConstant38| := le_abs_self _
  have hR3 : (0 : ℝ) ≤ R ^ 3 := by positivity
  have hR4 : (0 : ℝ) ≤ R ^ 4 / |(n : ℝ)| ^ 2 := by positivity
  constructor
  · show ‖actualSchurQn38 (4 * R) n (schurRealPair w) - (schurRealPair w).1 n‖ ≤ _
    calc ‖actualSchurQn38 (4 * R) n (schurRealPair w) - (schurRealPair w).1 n‖
        ≤ actualSchurBremConstant38 * (4 * R) ^ 4 / |(n : ℝ)| ^ 2 := hq
      _ = 256 * actualSchurBremConstant38 * (R ^ 4 / |(n : ℝ)| ^ 2) := by ring
      _ ≤ 256 * (|actualSchurBremConstant38| + 1) * (R ^ 4 / |(n : ℝ)| ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ hR4
          linarith
      _ = 256 * (|actualSchurBremConstant38| + 1) * R ^ 4 / |(n : ℝ)| ^ 2 := by ring
  · show ‖fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) n) w‖ ≤ _
    calc ‖fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) n) w‖
        ≤ actualSchurBremConstant38 * (4 * R) ^ 4 / |(n : ℝ)| ^ 2 / R := hd
      _ = 256 * actualSchurBremConstant38 * (R ^ 3 / |(n : ℝ)| ^ 2) := by
          field_simp
          ring
      _ ≤ 256 * (|actualSchurBremConstant38| + 1) * (R ^ 3 / |(n : ℝ)| ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith
      _ = 256 * (|actualSchurBremConstant38| + 1) * R ^ 3 / |(n : ℝ)| ^ 2 := by ring

end NlsGge.ThirdConsultation.S
