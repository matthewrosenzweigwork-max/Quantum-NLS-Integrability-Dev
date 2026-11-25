import NlsGge.Schur.ActualSchurFGboundAfterResolventFactorizationV5_31

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- The concrete ordered product `\widetilde G_n G_n` occurring in the
spectral derivative of the effective Schur operator. -/
def actualSchurGreenDerivativeProductV3_31 (n : ℤ) (z : ℂ)
    (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) : ParityPair n →L[ℂ] ParityPair n :=
  (actualSchurGreenRowV5_31 n z p hz).comp
    (actualSchurGreenColumnV5_31 n z p hz)

/-- The actual Schur derivative product has source scale `C R^4/n^2` on
the unchanged complex spectral disk and two independent H¹ balls. This is a
quantitative product estimate only; it does not assert a derivative identity. -/
theorem actualSchurGreenDerivativeProduct_boundV3_31
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ‖actualSchurGreenDerivativeProductV3_31 n z p hz‖ ≤
      freeResolventComplementaryInverseUniformConstant22 ^ 2 *
        freeResolventSchurUniformConstant ^ 2 * R ^ 4 / |(n : ℝ)| ^ 2 := by
  have hden : 0 < |(n : ℝ)| := by positivity
  have hRnonneg : 0 ≤ R := le_trans (by norm_num) hR
  have hInvCpos : 0 < freeResolventComplementaryInverseUniformConstant22 :=
    freeResolventComplementaryInverseUniformConstant22_posV2_31
  have hSchurCnonneg : 0 ≤ freeResolventSchurUniformConstant := by
    unfold freeResolventSchurUniformConstant
    positivity
  have hbound_nonneg :
      0 ≤ freeResolventComplementaryInverseUniformConstant22 *
        freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)| := by
    apply div_nonneg
    · exact mul_nonneg
        (mul_nonneg (le_of_lt hInvCpos) hSchurCnonneg) (sq_nonneg R)
    · exact le_of_lt hden
  have hrow := actualSchurGreenRow_boundV5_31 R hR n hn hlarge z p hz hp₁ hp₂
  have hcolumn := actualSchurGreenColumn_boundV5_31 R hR n hn hlarge z p hz hp₁ hp₂
  calc
    ‖actualSchurGreenDerivativeProductV3_31 n z p hz‖ ≤
        ‖actualSchurGreenRowV5_31 n z p hz‖ *
          ‖actualSchurGreenColumnV5_31 n z p hz‖ := by
            exact (actualSchurGreenRowV5_31 n z p hz).opNorm_comp_le _
    _ ≤ (freeResolventComplementaryInverseUniformConstant22 *
          freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)|) ^ 2 := by
            rw [pow_two]
            exact mul_le_mul hrow hcolumn
              (actualSchurGreenColumnV5_31 n z p hz).opNorm_nonneg hbound_nonneg
    _ = freeResolventComplementaryInverseUniformConstant22 ^ 2 *
          freeResolventSchurUniformConstant ^ 2 * R ^ 4 / |(n : ℝ)| ^ 2 := by ring

end NlsGge.Schur
