import NlsGge.Schur.ActualCoordinateDextDerivativeTransportMinimumV3_31
import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false
noncomputable section
open scoped Topology RightActions

namespace NlsGge.Schur

/-- Isolate the actual final coordinate-Dext `HasFDerivAt` transport. The
source derivative is the inverse-rule formula with the concrete unit inverse;
the conclusion attaches its explicitly typed derivative map to the named
actual Dext function. -/
theorem actualCoordinateDext_hasFDerivAt_namedFunctionTransportMinimumV5_32
    (n : ℤ) (z : ℂ)
    (hunit : IsUnit (1 + (z - spectralCenter n) •
      actualCoordinateCenterD0NamedFunctionMinimumV1_30 n))
    (hsource :
      let E : Type := SectorSquare n →L[ℂ] SectorSquare n
      let D₀ : E := actualCoordinateCenterD0NamedFunctionMinimumV1_30 n
      let Iunit : E :=
        ((hunit.unit⁻¹ : Eˣ) : E)
      HasFDerivAt
        (fun w : ℂ => Ring.inverse (1 + (w - spectralCenter n) • D₀) * D₀)
        (((-ContinuousLinearMap.mulLeftRight ℂ E Iunit Iunit).comp
          (ContinuousLinearMap.toSpanSingleton ℂ D₀)) <• D₀) z) :
    let E : Type := SectorSquare n →L[ℂ] SectorSquare n
    let D₀ : E := actualCoordinateCenterD0NamedFunctionMinimumV1_30 n
    let I : E := Ring.inverse (1 + (z - spectralCenter n) • D₀)
    HasFDerivAt
      (actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30 n)
      (((-ContinuousLinearMap.mulLeftRight ℂ E I I).comp
        (ContinuousLinearMap.toSpanSingleton ℂ D₀)) <• D₀) z := by
  dsimp
  let E : Type := SectorSquare n →L[ℂ] SectorSquare n
  letI : NormedRing E := ContinuousLinearMap.toNormedRing
  letI : NonUnitalNormedRing E := NormedRing.toNonUnitalNormedRing
  letI : NormedAddCommGroup E := NonUnitalNormedRing.toNormedAddCommGroup
  letI : NormedAlgebra ℂ E := ContinuousLinearMap.toNormedAlgebra
  letI : NormedSpace ℂ E := ContinuousLinearMap.toNormedSpace
  let D₀ : E := actualCoordinateCenterD0NamedFunctionMinimumV1_30 n
  let Iunit : E := ((hunit.unit⁻¹ : Eˣ) : E)
  let I : E := Ring.inverse (1 + (z - spectralCenter n) • D₀)
  have hI : Iunit = I := by
    simpa only [Iunit, I, D₀, E] using
      actualCoordinateCenterFactor_unitInverse_eq_ringInverseMinimumV3_31
        n z hunit
  have hderiv :
      (((-ContinuousLinearMap.mulLeftRight ℂ E Iunit Iunit).comp
        (ContinuousLinearMap.toSpanSingleton ℂ D₀)) <• D₀) =
      (((-ContinuousLinearMap.mulLeftRight ℂ E I I).comp
        (ContinuousLinearMap.toSpanSingleton ℂ D₀)) <• D₀) := by
    simp only [hI]
  have hnormalized := hsource.congr_fderiv hderiv
  have hmodule := actualCoordinateDextDerivativeModuleDictionary_minimumV1_31 n
  cases hmodule
  have hfunction :
      (fun w : ℂ =>
        Ring.inverse (1 + (w - spectralCenter n) • D₀) * D₀) =
        actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30 n := by
    simpa only [D₀] using!
      actualCoordinateFreeResolventCenterExtension_functionModuleCoherenceMinimumV1_30 n
  exact hnormalized.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => congrFun hfunction.symm x)

end NlsGge.Schur
