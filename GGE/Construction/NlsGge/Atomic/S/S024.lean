import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurF03Package38V1
import NlsGge.Spectral.ActualBoxWindowUniformE02_38
import NlsGge.Spectral.ActualGapLabelsAgreeE02_38

                                                                                                           
                                                                                                                    
                                                                                                                 
                                                                               
                                                                                                      
                                                                                                                         
                                                                                                                   
                                                                                                                     
                                                                                                               
                                               

set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
open NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.S

theorem highGap_displacement_bound :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (n : ℤ),
      K * R ^ 3 ≤ |(n : ℝ)| → ∀ (w : SchurH1), ‖w‖ ≤ R →
      max |actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n - Real.pi * n|
        |actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n - Real.pi * n| ≤
        C * R ^ 3 / |(n : ℝ)| := by
  obtain ⟨Kp, hKp, hpack⟩ := actualSchurF03Package38V1
  obtain ⟨K1, C1, hK1, hC1, hbw⟩ := actualBoxWindow_uniform_E02_38
  refine ⟨|actualSchurGapLocalConstant38| + 1, max Kp K1, by positivity,
    lt_of_lt_of_le hKp (le_max_left _ _), ?_⟩
  intro R hR n hn w hwR
  have hR0 : 0 ≤ R := by linarith
  have hR3 : 0 ≤ R ^ 3 := pow_nonneg hR0 3
  have hR2 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR (by norm_num)
  have hnp : Kp * R ^ 3 ≤ |((-n : ℤ) : ℝ)| := by
    rw [Int.cast_neg, abs_neg]
    exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR3) hn
  have hnw : K1 * R ^ 2 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_left hR2 hK1.le)
      (le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hR3) hn)
  set U := physicalH1ComplexCarrierToL2Actual22 w with hU
  have hu := physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w
  have hnorm : ‖physicalSobolevL2 1 U hu‖ ≤ R := by
    rw [physicalSobolevL2_norm_h1Carrier38]; exact hwR
  obtain ⟨⟨lp, lm, ⟨hlpI, hlpF⟩, ⟨hlmI, hlmF⟩⟩, hall⟩ := hpack R hR (-n) hnp w hwR
  obtain ⟨-, -, ⟨hc1, hc2⟩, -⟩ := hall lp lm hlpI hlpF hlmI hlmF
  obtain ⟨hbox, hδ, hwin⟩ := hbw R hR U hu hnorm n hnw
  obtain ⟨hlo, hup, -⟩ := actualGapLabels_agree_E02_38 U n _
    (div_nonneg (mul_nonneg hC1.le (sq_nonneg R)) (abs_nonneg _)) hδ hbox hwin
  simp only [neg_neg, Int.cast_neg, abs_neg] at hc1 hc2
  rw [hlo] at hc1
  rw [hup] at hc2
  have hca : |actualGapLowerAllE02_38 U n - Real.pi * n| ≤
      actualSchurGapLocalConstant38 * R ^ 3 / |(n : ℝ)| := by
    convert hc1 using 2; ring
  have hcb : |actualGapUpperAllE02_38 U n - Real.pi * n| ≤
      actualSchurGapLocalConstant38 * R ^ 3 / |(n : ℝ)| := by
    convert hc2 using 2; ring
  have hC : actualSchurGapLocalConstant38 * R ^ 3 / |(n : ℝ)| ≤
      (|actualSchurGapLocalConstant38| + 1) * R ^ 3 / |(n : ℝ)| :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith [le_abs_self actualSchurGapLocalConstant38]) hR3)
      (abs_nonneg _)
  exact max_le (le_trans hca hC) (le_trans hcb hC)

end NlsGge.ThirdConsultation.S
