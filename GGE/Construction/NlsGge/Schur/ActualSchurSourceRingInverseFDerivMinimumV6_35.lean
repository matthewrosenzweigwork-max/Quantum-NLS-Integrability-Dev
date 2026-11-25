import NlsGge.Schur.ActualSchurCLMUnitsAndParentedInverseValueMinimumV2_35
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
noncomputable section
open scoped Topology RightActions

namespace NlsGge.Schur

/-- The actual source-parent total inverse is differentiable at every unit
of the coherent normed-ring parent. The unit binder and the inverse function
used to name its `fderiv` both explicitly carry that normed-ring parent. -/
theorem actualSchurSourceRingInverseHasFDerivAtFDerivMinimumV6_35
    (n : ℤ) :
    let E : Type := ParityPair n →L[ℂ] ParityPair n
    letI : NormedRing E := ContinuousLinearMap.toNormedRing
    letI : NonUnitalNormedRing E := NormedRing.toNonUnitalNormedRing
    letI : NormedAddCommGroup E := NonUnitalNormedRing.toNormedAddCommGroup
    letI : NormedAlgebra ℂ E := ContinuousLinearMap.toNormedAlgebra
    letI : NormedSpace ℂ E := NormedAlgebra.toNormedSpace E
    ∀ u : @Units E (actualSchurCLMRingMonoidWithZeroV3_34 n).toMonoid,
      HasFDerivAt
        (fun T : E =>
          @Ring.inverse E (actualSchurCLMSourceMonoidWithZeroV3_34 n) T)
        (fderiv ℂ
          (fun T : E =>
            @Ring.inverse E (actualSchurCLMRingMonoidWithZeroV3_34 n) T)
          (u : E))
        (u : E) := by
  intro E
  intro u
  let sourceInverse : E → E :=
    fun T => @Ring.inverse E (actualSchurCLMSourceMonoidWithZeroV3_34 n) T
  let ringInverse : E → E :=
    fun T => @Ring.inverse E (actualSchurCLMRingMonoidWithZeroV3_34 n) T
  have hbase : HasFDerivAt ringInverse
      (fderiv ℂ ringInverse (u : E))
      (u : E) := by
    exact (hasFDerivAt_ringInverse (𝕜 := ℂ) u).differentiableAt.hasFDerivAt
  have hsame : sourceInverse =ᶠ[𝓝 (u : E)] ringInverse :=
    Filter.Eventually.of_forall fun T =>
      actualSchurParentedTotalInverseValueAgreementV2_35 n T
  exact hbase.congr_of_eventuallyEq hsame

end NlsGge.Schur
