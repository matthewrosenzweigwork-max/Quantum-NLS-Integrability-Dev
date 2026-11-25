import Mathlib
import NlsGge.Schur.ActualSchurCenterAnalytic38V1
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                            
                                                                                                                        
                                                                                                              
                                                                                                                     
                                                                                                  
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem schurBallMap_analytic (M N : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : schurAllThreshold * R ^ 6 ≤ (M : ℝ)) :
    AnalyticOnNhd ℝ (schurBallMap M N) (schurH1Ball N R) := by
  intro z hz
  have hz' : ‖planeH1Embedding38 N z‖ < R := hz
  unfold schurBallMap
  rw [analyticAt_pi_iff]
  intro i
  by_cases hi : (modeIndex N i).natAbs ≤ M
  · have h : (fun z' : FourierPlane N => actualSchurBallMap38 N M z' i) =
        fun z' => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * N + 1) => ℂ) i) z' := by
      funext z'; exact actualSchurBallMap38_low N M z' i hi
    rw [h]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * N + 1) => ℂ) i).analyticAt z
  · have hR0 : 0 ≤ R := by linarith
    have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
    have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR
    have h36 : R ^ 3 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
    have hK := abs_nonneg actualSchurCenterThresholdConstant38
    have hA : 512 * |actualSchurCenterThresholdConstant38| ≤ schurAllThreshold := by
      unfold schurAllThreshold
      have := abs_nonneg schurCommonThreshold
      have := abs_nonneg actualSchurShiftedRootsConstant38
      have := abs_nonneg actualSchurGapLocalConstant38
      have := abs_nonneg (freeResolventComplementaryInverseUniformConstant22 ^ 2 *
        freeResolventSchurUniformConstant ^ 2)
      linarith
    have hn := natAbs_gt_abs38 M _ hi
    have hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |((modeIndex N i : ℤ) : ℝ)| := by
      have h1 : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |actualSchurCenterThresholdConstant38| * R ^ 6 :=
        calc _ ≤ |actualSchurCenterThresholdConstant38| * R ^ 3 :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left h36 hK
      have h2 : |actualSchurCenterThresholdConstant38| * R ^ 6 ≤ schurAllThreshold * R ^ 6 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have hqa : AnalyticAt ℝ (fun z' : FourierPlane N =>
        actualSchurQn38 R (modeIndex N i)
          (actualRealTypeEmbedding38 (planeH1EmbeddingR38 N z'))) z := by
      have hq := actualSchurQn38_analyticAt R hR (modeIndex N i) hthr
        (planeH1Embedding38 N z, actualH1Conj38 (planeH1Embedding38 N z)) hz'
        (by rw [actualH1Conj38_norm]; exact hz')
      have hqR : AnalyticAt ℝ (actualSchurQn38 R (modeIndex N i))
          (actualRealTypeEmbedding38 (planeH1EmbeddingR38 N z)) := hq.restrictScalars (𝕜 := ℝ)
      have hι : AnalyticAt ℝ (fun z' : FourierPlane N =>
          actualRealTypeEmbedding38 (planeH1EmbeddingR38 N z')) z :=
        (actualRealTypeEmbedding38.comp (planeH1EmbeddingR38 N)).analyticAt z
      exact AnalyticAt.comp (g := actualSchurQn38 R (modeIndex N i))
        (f := fun z' : FourierPlane N => actualRealTypeEmbedding38 (planeH1EmbeddingR38 N z')) hqR hι
    have hopen : IsOpen {z' : FourierPlane N | ‖planeH1Embedding38 N z'‖ < R} :=
      isOpen_lt (planeH1Embedding38 N).continuous.norm continuous_const
    have hev : (fun z' : FourierPlane N => actualSchurQn38 R (modeIndex N i)
          (actualRealTypeEmbedding38 (planeH1EmbeddingR38 N z'))) =ᶠ[nhds z]
        (fun z' : FourierPlane N => actualSchurBallMap38 N M z' i) := by
      filter_upwards [hopen.mem_nhds hz'] with z' hz''
      have hz3 : ‖planeH1Embedding38 N z'‖ < R := hz''
      rw [actualSchurBallMap38_high N M z' i hi]
      have hc := actualSchurQnCanonical38_eq R hR _ hthr
        (planeH1Embedding38 N z', actualH1Conj38 (planeH1Embedding38 N z')) hz3.le
        (by rw [actualH1Conj38_norm]; exact hz3.le)
      rw [actualRealTypeEmbedding38_apply, planeH1EmbeddingR38_apply]
      exact hc.symm
    exact hqa.congr hev

end NlsGge.ThirdConsultation.S

end
