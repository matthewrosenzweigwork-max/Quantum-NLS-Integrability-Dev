import NlsGge.Schur.ActualSchurBallMapJacobian38V1

                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S


def schurBallMap (M N : ℕ) : FourierPlane N → FourierPlane N :=
  actualSchurBallMap38 N M

def schurH1Ball (N : ℕ) (R : ℝ) : Set (FourierPlane N) :=
  {z | planeH1Norm38 N z < R}

def schurRealJacobianDet (M N : ℕ) (z : FourierPlane N) : ℝ :=
  LinearMap.det
    (fderiv ℝ (schurBallMap M N) z : FourierPlane N →ₗ[ℝ] FourierPlane N)

def schurCommonThreshold : ℝ :=
  1 + |actualSchurJacobianMConstant38| +
    64 * |actualSchurCenterThresholdConstant38|

theorem schurCommonThreshold_hyps (R : ℝ) (hR : 1 ≤ R) (M : ℕ)
    (hM : schurCommonThreshold * R ^ 6 ≤ (M : ℝ)) :
    actualSchurJacobianMConstant38 * R ^ 6 ≤ (M : ℝ) ∧
    actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ) := by
  have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hR36 : R ^ 3 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
  have hJ := actualSchurJacobianMConstant38_ge_one
  have hJabs : actualSchurJacobianMConstant38 ≤ schurCommonThreshold := by
    unfold schurCommonThreshold
    have := abs_nonneg actualSchurCenterThresholdConstant38
    rw [abs_of_nonneg (by linarith : 0 ≤ actualSchurJacobianMConstant38)]
    linarith
  have hKabs : 64 * |actualSchurCenterThresholdConstant38| ≤ schurCommonThreshold := by
    unfold schurCommonThreshold
    have := abs_nonneg actualSchurJacobianMConstant38
    linarith
  constructor
  · exact (mul_le_mul_of_nonneg_right hJabs (by positivity)).trans hM
  · have h1 : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤
        64 * |actualSchurCenterThresholdConstant38| * R ^ 3 := by
      have : (4 * R) ^ 3 = 64 * R ^ 3 := by ring
      rw [this]
      nlinarith [le_abs_self actualSchurCenterThresholdConstant38, abs_nonneg actualSchurCenterThresholdConstant38]
    refine h1.trans ?_
    calc 64 * |actualSchurCenterThresholdConstant38| * R ^ 3
        ≤ schurCommonThreshold * R ^ 3 := mul_le_mul_of_nonneg_right hKabs (by positivity)
      _ ≤ schurCommonThreshold * R ^ 6 := by
          apply mul_le_mul_of_nonneg_left hR36
          unfold schurCommonThreshold
          have := abs_nonneg actualSchurJacobianMConstant38
          have := abs_nonneg actualSchurCenterThresholdConstant38
          linarith
      _ ≤ (M : ℝ) := hM

theorem schurBallMap_common_absolute_threshold :
    ∃ A : ℝ, 0 < A ∧ ∀ (R : ℝ), 1 ≤ R →
      ∀ (M N : ℕ), A * R ^ 6 ≤ (M : ℝ) →
        Set.InjOn (schurBallMap M N) (schurH1Ball N R) ∧
        (∀ z : FourierPlane N, z ∈ schurH1Ball N R →
          schurRealJacobianDet M N z ∈ Set.Icc (1 / 2 : ℝ) 2) := by
  refine ⟨schurCommonThreshold, ?_, ?_⟩
  · unfold schurCommonThreshold
    have := abs_nonneg actualSchurJacobianMConstant38
    have := abs_nonneg actualSchurCenterThresholdConstant38
    linarith
  · intro R hR M N hM
    obtain ⟨h1, h2⟩ := schurCommonThreshold_hyps R hR M hM
    exact ⟨actualSchurBallMap38_injOn N M R hR h1 h2,
      fun z hz => actualSchurBallMap38_det_mem_Icc N M R hR h1 h2 z hz⟩

theorem schurBallMap_injOn (M N : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : schurCommonThreshold * R ^ 6 ≤ (M : ℝ)) :
    Set.InjOn (schurBallMap M N) (schurH1Ball N R) := by
  obtain ⟨h1, h2⟩ := schurCommonThreshold_hyps R hR M hM
  exact actualSchurBallMap38_injOn N M R hR h1 h2

end NlsGge.ThirdConsultation.S
