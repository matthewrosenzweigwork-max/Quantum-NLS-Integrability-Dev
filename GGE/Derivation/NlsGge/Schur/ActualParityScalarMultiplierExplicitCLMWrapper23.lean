import NlsGge.Schur.ActualParityScalarMultiplierNormOnlyPrerequisite23

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

local notation "H1WeightScalarWrapper23" => sobolevModeWeight (1 : ℝ)
local notation "H1ScalarCarrierWrapper23" => WeightedHilbert H1WeightScalarWrapper23

/-- The actual continuous scalar multiplier, constructed from the checked
linear map and its exact operator bound with the concrete complex module types. -/
def actualParityScalarMultiplierParameterExplicitCLM23 (n : ℤ) :
    H1ScalarCarrierWrapper23 →L[ℂ] (scalarParity n →L[ℂ] scalarParity n) := by
  let f : H1ScalarCarrierWrapper23 →ₗ[ℂ]
      (scalarParity n →L[ℂ] scalarParity n) :=
    actualParityScalarMultiplierParameterLinearNormOnly23 n
  exact
    { toLinearMap := f
      cont := AddMonoidHomClass.continuous_of_bound f
        ‖physicalH1ComplexScalarMultiplierParameterCLM22‖
        (actualParityScalarMultiplierParameterLinearNormOnly23_norm_le n) }

@[simp] theorem actualParityScalarMultiplierParameterExplicitCLM23_apply
    (n : ℤ) (x : H1ScalarCarrierWrapper23) :
    actualParityScalarMultiplierParameterExplicitCLM23 n x =
      coveredH1ScalarParityMultiplier
        (physicalH1ComplexCarrierToL2Actual22 x)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x) n := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  rfl

end NlsGge.Schur
