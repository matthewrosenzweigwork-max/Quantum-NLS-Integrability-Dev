import NlsGge.Schur.PhysicalH1ComplexMultiplierParameterAfterCanonicalRepresentative
import NlsGge.Schur.CoveredH1ParityPairOperatorFromAE
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

local notation "H1WeightScalarNormOnly23" => sobolevModeWeight (1 : ℝ)
local notation "H1ScalarCarrierNormOnly23" => WeightedHilbert H1WeightScalarNormOnly23

/-- Actual scalar multiplier restriction, linear in the actual complex H¹
Fourier potential parameter. -/
def actualParityScalarMultiplierParameterLinearNormOnly23 (n : ℤ) :
    H1ScalarCarrierNormOnly23 →ₗ[ℂ]
      (scalarParity n →L[ℂ] scalarParity n) where
  toFun x := coveredH1ScalarParityMultiplier
    (physicalH1ComplexCarrierToL2Actual22 x)
    (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x) n
  map_add' x y := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    change coveredH1SpectralMultiplier
        (physicalH1ComplexCarrierToL2Actual22 (x + y))
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable (x + y)) f.val =
      coveredH1SpectralMultiplier
        (physicalH1ComplexCarrierToL2Actual22 x)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x) f.val +
      coveredH1SpectralMultiplier
        (physicalH1ComplexCarrierToL2Actual22 y)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable y) f.val
    rw [← physicalH1ComplexScalarMultiplierParameterCLM22_apply (x + y),
      ← physicalH1ComplexScalarMultiplierParameterCLM22_apply x,
      ← physicalH1ComplexScalarMultiplierParameterCLM22_apply y]
    simp only [physicalH1ComplexScalarMultiplierParameterCLM22.map_add,
      ContinuousLinearMap.add_apply]
  map_smul' c x := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    change coveredH1SpectralMultiplier
        (physicalH1ComplexCarrierToL2Actual22 (c • x))
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable (c • x)) f.val =
      c • coveredH1SpectralMultiplier
        (physicalH1ComplexCarrierToL2Actual22 x)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x) f.val
    rw [← physicalH1ComplexScalarMultiplierParameterCLM22_apply (c • x),
      ← physicalH1ComplexScalarMultiplierParameterCLM22_apply x]
    simp only [physicalH1ComplexScalarMultiplierParameterCLM22.map_smul,
      ContinuousLinearMap.smul_apply]

/-- The actual scalar restricted multiplier parameter has the same bound as
the checked ambient multiplier parameter operator. -/
theorem actualParityScalarMultiplierParameterLinearNormOnly23_norm_le
    (n : ℤ) (x : H1ScalarCarrierNormOnly23) :
    ‖actualParityScalarMultiplierParameterLinearNormOnly23 n x‖ ≤
      ‖physicalH1ComplexScalarMultiplierParameterCLM22‖ * ‖x‖ := by
  change ‖coveredH1ScalarParityMultiplier
      (physicalH1ComplexCarrierToL2Actual22 x)
      (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x) n‖ ≤
    ‖physicalH1ComplexScalarMultiplierParameterCLM22‖ * ‖x‖
  let M : scalarParity n →L[ℂ] scalarParity n := coveredH1ScalarParityMultiplier
    (physicalH1ComplexCarrierToL2Actual22 x)
    (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x) n
  change ‖M‖ ≤ ‖physicalH1ComplexScalarMultiplierParameterCLM22‖ * ‖x‖
  apply ContinuousLinearMap.opNorm_le_bound M
    (mul_nonneg
      (norm_nonneg physicalH1ComplexScalarMultiplierParameterCLM22)
      (norm_nonneg x))
  intro f
  change ‖coveredH1SpectralMultiplier
      (physicalH1ComplexCarrierToL2Actual22 x)
      (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x) f.val‖ ≤
    (‖physicalH1ComplexScalarMultiplierParameterCLM22‖ * ‖x‖) * ‖f‖
  rw [← physicalH1ComplexScalarMultiplierParameterCLM22_apply x]
  calc
    ‖physicalH1ComplexScalarMultiplierParameterCLM22 x f.val‖ ≤
        ‖physicalH1ComplexScalarMultiplierParameterCLM22 x‖ * ‖f.val‖ :=
      (physicalH1ComplexScalarMultiplierParameterCLM22 x).le_opNorm f.val
    _ ≤ (‖physicalH1ComplexScalarMultiplierParameterCLM22‖ * ‖x‖) * ‖f.val‖ :=
      mul_le_mul_of_nonneg_right
        (physicalH1ComplexScalarMultiplierParameterCLM22.le_opNorm x)
        (norm_nonneg _)
    _ = (‖physicalH1ComplexScalarMultiplierParameterCLM22‖ * ‖x‖) * ‖f‖ := by
      rw [Submodule.norm_coe]

end NlsGge.Schur
