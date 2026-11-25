import NlsGge.Schur.CoveredH1ParityPairOperatorFromAE

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- The off-diagonal pair multiplication norm is bounded by the sum of the
two actual scalar multiplier norms. -/
theorem coveredH1ParityPairPotential_norm_le_scalar_sum
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) (n : ℤ) :
    ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n‖ ≤
      ‖coveredH1SpectralMultiplier u₁ hu₁‖ +
        ‖coveredH1SpectralMultiplier u₂ hu₂‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  have hpi : ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x‖ ^ 2 =
      ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x true‖ ^ 2 +
        ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x false‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Fintype.sum_bool]
  have hxtrue : ‖x true‖ ≤ ‖x‖ := PiLp.norm_apply_le x true
  have hxfalse : ‖x false‖ ≤ ‖x‖ := PiLp.norm_apply_le x false
  have houttrue :
      ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x true‖ ≤
        ‖coveredH1SpectralMultiplier u₁ hu₁‖ * ‖x false‖ := by
    rw [coveredH1ParityPairPotential_apply_true]
    calc
      ‖coveredH1ScalarParityMultiplier u₁ hu₁ n (x false)‖ =
          ‖coveredH1SpectralMultiplier u₁ hu₁ (x false).val‖ := by
            rw [← Submodule.norm_coe (coveredH1ScalarParityMultiplier u₁ hu₁ n (x false))]
            rw [coveredH1ScalarParityMultiplier_coe_apply]
      _ ≤ ‖coveredH1SpectralMultiplier u₁ hu₁‖ * ‖(x false).val‖ :=
          (coveredH1SpectralMultiplier u₁ hu₁).le_opNorm _
      _ = ‖coveredH1SpectralMultiplier u₁ hu₁‖ * ‖x false‖ := by
          rw [Submodule.norm_coe]
  have houtfalse :
      ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x false‖ ≤
        ‖coveredH1SpectralMultiplier u₂ hu₂‖ * ‖x true‖ := by
    rw [coveredH1ParityPairPotential_apply_false]
    calc
      ‖coveredH1ScalarParityMultiplier u₂ hu₂ n (x true)‖ =
          ‖coveredH1SpectralMultiplier u₂ hu₂ (x true).val‖ := by
            rw [← Submodule.norm_coe (coveredH1ScalarParityMultiplier u₂ hu₂ n (x true))]
            rw [coveredH1ScalarParityMultiplier_coe_apply]
      _ ≤ ‖coveredH1SpectralMultiplier u₂ hu₂‖ * ‖(x true).val‖ :=
          (coveredH1SpectralMultiplier u₂ hu₂).le_opNorm _
      _ = ‖coveredH1SpectralMultiplier u₂ hu₂‖ * ‖x true‖ := by
          rw [Submodule.norm_coe]
  have hsum :
      ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x true‖ +
        ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x false‖ ≤
        (‖coveredH1SpectralMultiplier u₁ hu₁‖ +
          ‖coveredH1SpectralMultiplier u₂ hu₂‖) * ‖x‖ := by
    calc
      _ ≤ ‖coveredH1SpectralMultiplier u₁ hu₁‖ * ‖x false‖ +
          ‖coveredH1SpectralMultiplier u₂ hu₂‖ * ‖x true‖ :=
        add_le_add houttrue houtfalse
      _ ≤ _ := by
        rw [add_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hxfalse (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hxtrue (norm_nonneg _))
  have htriangle :
      ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x‖ ≤
        ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x true‖ +
          ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x false‖ := by
    have htrue := norm_nonneg
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x true)
    have hfalse := norm_nonneg
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x false)
    have hpair := norm_nonneg (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x)
    nlinarith [hpi, htrue, hfalse, hpair, sq_nonneg
      (‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x true‖ -
        ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n x false‖)]
  exact htriangle.trans hsum

/-- On the same physical H¹ radius `R`, the actual paired potential has a
uniform bound with both independent fields retained. -/
theorem coveredH1ParityPairPotential_norm_bound
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) (n : ℤ) (R : ℝ)
    (hR : 0 ≤ R)
    (h₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R)
    (h₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R) :
    ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n‖ ≤
      2 * physicalH1MultiplierConstant * R := by
  calc
    ‖coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n‖ ≤
        ‖coveredH1SpectralMultiplier u₁ hu₁‖ +
          ‖coveredH1SpectralMultiplier u₂ hu₂‖ :=
      coveredH1ParityPairPotential_norm_le_scalar_sum u₁ u₂ hu₁ hu₂ n
    _ ≤ physicalH1MultiplierConstant *
          ‖physicalSobolevL2 1 u₁ hu₁‖ +
        physicalH1MultiplierConstant * ‖physicalSobolevL2 1 u₂ hu₂‖ :=
      add_le_add (coveredH1SpectralMultiplier_norm_bound u₁ hu₁)
        (coveredH1SpectralMultiplier_norm_bound u₂ hu₂)
    _ ≤ 2 * physicalH1MultiplierConstant * R := by
      have hC := physicalH1MultiplierConstant_pos.le
      nlinarith

end NlsGge.Schur
