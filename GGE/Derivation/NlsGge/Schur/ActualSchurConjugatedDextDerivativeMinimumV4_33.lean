import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30
import NlsGge.Schur.ActualCoordinateDextHasFDerivAtNegativeSquareV4_32
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv

set_option autoImplicit false
noncomputable section
open scoped Topology RightActions

namespace NlsGge.Schur

/-- Transport the checked coordinate Dext derivative through the actual
Fourier-conjugacy algebra equivalence. This isolates the Dext derivative
transport from the later QVD inverse and product-rule argument. -/
theorem actualFreeResolventCenterExtension_hasFDerivAt_negativeSquareMinimumV4_33
    (n : ℤ) (z : ℂ)
    (hz : z ∈ Metric.ball (spectralCenter n) 2) :
    HasFDerivAt
      (actualFreeResolventCenterExtensionV1_30 n)
      (ContinuousLinearMap.toSpanSingleton ℂ
        (-(actualFreeResolventCenterExtensionV1_30 n z).comp
          (actualFreeResolventCenterExtensionV1_30 n z))) z := by
  let Ec : Type := SectorSquare n →L[ℂ] SectorSquare n
  let Ep : Type := ParityPair n →L[ℂ] ParityPair n
  letI : NormedRing Ec := ContinuousLinearMap.toNormedRing
  letI : NonUnitalNormedRing Ec := NormedRing.toNonUnitalNormedRing
  letI : NormedAddCommGroup Ec := NonUnitalNormedRing.toNormedAddCommGroup
  letI : NormedAlgebra ℂ Ec := ContinuousLinearMap.toNormedAlgebra
  letI : NormedSpace ℂ Ec := ContinuousLinearMap.toNormedSpace
  letI : NormedRing Ep := ContinuousLinearMap.toNormedRing
  letI : NonUnitalNormedRing Ep := NormedRing.toNonUnitalNormedRing
  letI : NormedAddCommGroup Ep := NonUnitalNormedRing.toNormedAddCommGroup
  letI : NormedAlgebra ℂ Ep := ContinuousLinearMap.toNormedAlgebra
  letI : NormedSpace ℂ Ep := ContinuousLinearMap.toNormedSpace

  let Dcoord : ℂ → Ec := actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30 n
  let Φ := actualCoordinatePairEndomorphismConjugacyV2_26 n
  let C : Ec →L[ℂ] Ep := Φ.toContinuousLinearEquiv.toContinuousLinearMap
  let D : ℂ → Ep := actualFreeResolventCenterExtensionV1_30 n

  have hDcoord := actualCoordinateDext_hasFDerivAt_negativeSquareV4_32 n z hz
  have hDconj : D = fun w => C (Dcoord w) := by
    funext w
    rfl
  have hDmap : C.comp
      (ContinuousLinearMap.toSpanSingleton ℂ (-(Dcoord z).comp (Dcoord z))) =
      ContinuousLinearMap.toSpanSingleton ℂ (-(D z).comp (D z)) := by
    apply ContinuousLinearMap.ext
    intro δ
    change C (δ • (-(Dcoord z).comp (Dcoord z))) =
      δ • (-(D z).comp (D z))
    rw [C.map_smul]
    change δ • Φ (-(Dcoord z).comp (Dcoord z)) =
      δ • (-(D z).comp (D z))
    have hmulCLM : C ((Dcoord z).comp (Dcoord z)) =
        (C (Dcoord z)).comp (C (Dcoord z)) := by
      simpa only [C, Φ, ContinuousLinearMap.mul_def] using!
        Φ.map_mul (Dcoord z) (Dcoord z)
    have hneg : Φ (-(Dcoord z).comp (Dcoord z)) =
        -(Φ ((Dcoord z).comp (Dcoord z))) := by
      simpa only using! Φ.toRingEquiv.map_neg
        ((Dcoord z).comp (Dcoord z))
    have hDvalue : D z = Φ (Dcoord z) := by rfl
    rw [hneg, hDvalue]
    have hscaled := congrArg (fun T : Ep => δ • (-T)) hmulCLM
    simpa only [C, Φ] using! hscaled
  have hraw : HasFDerivAt (fun w => C (Dcoord w))
      (C.comp (ContinuousLinearMap.toSpanSingleton ℂ
        (-(Dcoord z).comp (Dcoord z)))) z := by
    exact (C.hasFDerivAt).comp z hDcoord
  rw [← hDconj] at hraw
  exact hraw.congr_fderiv hDmap

end NlsGge.Schur
