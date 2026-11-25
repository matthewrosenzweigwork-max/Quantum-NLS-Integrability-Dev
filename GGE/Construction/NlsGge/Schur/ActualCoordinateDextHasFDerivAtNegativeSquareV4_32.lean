import NlsGge.Schur.ActualCoordinateDextHasFDerivAtTransportMinimumV5_32
import NlsGge.Schur.ActualCoordinateDextDerivativeTransportMinimumV3_31
import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30
import NlsGge.Schur.ActualCoordinateDextNegativeSquareOperatorIdentityMinimumV3_32
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
noncomputable section
open scoped Topology RightActions

namespace NlsGge.Schur

/-- The actual coordinate free-resolvent extension has derivative equal to
minus its own square throughout the original open radius-two center disk. The
inverse-rule derivative is first transported through the checked V5 named-
function minimum; a separate exact algebra identity converts its map to
`-D(z)^2`. -/
theorem actualCoordinateDext_hasFDerivAt_negativeSquareV4_32
    (n : ℤ) (z : ℂ)
    (hz : z ∈ Metric.ball (spectralCenter n) 2) :
    HasFDerivAt
      (actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30 n)
      (ContinuousLinearMap.toSpanSingleton ℂ
        (-(actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30 n z).comp
          (actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30 n z))) z := by
  let E : Type := SectorSquare n →L[ℂ] SectorSquare n
  letI : NormedRing E := ContinuousLinearMap.toNormedRing
  letI : NonUnitalNormedRing E := NormedRing.toNonUnitalNormedRing
  letI : NormedAddCommGroup E := NonUnitalNormedRing.toNormedAddCommGroup
  letI : NormedAlgebra ℂ E := ContinuousLinearMap.toNormedAlgebra
  letI : NormedSpace ℂ E := ContinuousLinearMap.toNormedSpace
  let D₀ : E := actualCoordinateCenterD0NamedFunctionMinimumV1_30 n
  let B : ℂ → E := fun w => 1 + (w - spectralCenter n) • D₀
  let I : E := Ring.inverse (B z)
  let D : E := actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30 n z

  have hlinear : HasDerivAt (fun w : ℂ => w - spectralCenter n) 1 z := by
    simpa using (hasDerivAt_id z).sub_const (spectralCenter n)
  have hsmul' := hlinear.hasFDerivAt.smul_const D₀
  have hsmul : HasFDerivAt (fun w : ℂ => (w - spectralCenter n) • D₀)
      (ContinuousLinearMap.toSpanSingleton ℂ D₀) z := by
    have hderiv :
        (ContinuousLinearMap.toSpanSingleton ℂ (1 : ℂ)).smulRight D₀ =
          ContinuousLinearMap.toSpanSingleton ℂ D₀ := by
      ext w
      simp
    simpa only [hderiv] using hsmul'
  have hB : HasFDerivAt B (ContinuousLinearMap.toSpanSingleton ℂ D₀) z := by
    simpa only [B] using hsmul.const_add (1 : E)

  have hunit : IsUnit (B z) := by
    simpa only [B, D₀] using
      actualCoordinateCenterFactor_isUnit_radiusTwoMinimumV3_31 n z hz
  have hu : (hunit.unit : E) = B z := hunit.unit_spec
  have hbase : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℂ E
        ((hunit.unit⁻¹ : Eˣ) : E) ((hunit.unit⁻¹ : Eˣ) : E)) (B z) := by
    simpa only [hu] using (hasFDerivAt_ringInverse (𝕜 := ℂ) hunit.unit)
  have hinv := hbase.comp z hB
  have hfinal := hinv.mul_const' D₀

  have hsource :
      let E : Type := SectorSquare n →L[ℂ] SectorSquare n
      let D₀ : E := actualCoordinateCenterD0NamedFunctionMinimumV1_30 n
      let Iunit : E := ((hunit.unit⁻¹ : Eˣ) : E)
      HasFDerivAt
        (fun w : ℂ => Ring.inverse (1 + (w - spectralCenter n) • D₀) * D₀)
        (((-ContinuousLinearMap.mulLeftRight ℂ E Iunit Iunit).comp
          (ContinuousLinearMap.toSpanSingleton ℂ D₀)) <• D₀) z := by
    simpa only [Function.comp_apply, B] using hfinal

  have htransport :=
    actualCoordinateDext_hasFDerivAt_namedFunctionTransportMinimumV5_32
      n z hunit hsource
  have hmap :
      (((-ContinuousLinearMap.mulLeftRight ℂ E I I).comp
        (ContinuousLinearMap.toSpanSingleton ℂ D₀)) <• D₀) =
      ContinuousLinearMap.toSpanSingleton ℂ (-(D.comp D)) := by
    simpa only [D, I, B,
      actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30,
      ContinuousLinearMap.mul_def] using
      actualCoordinateDextNegativeSquareOperatorIdentityMinimumV3_32 n z


  have htransport' := htransport.congr_fderiv hmap
  simpa only [D] using htransport'

end NlsGge.Schur
