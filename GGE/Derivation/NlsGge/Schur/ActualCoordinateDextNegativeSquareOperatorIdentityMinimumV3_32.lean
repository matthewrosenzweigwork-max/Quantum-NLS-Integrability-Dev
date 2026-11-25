import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30
import Mathlib.Analysis.Normed.Operator.Mul

set_option autoImplicit false
noncomputable section
open scoped Topology RightActions

namespace NlsGge.Schur

/-- Isolate the concrete coordinate endomorphism algebra needed to turn the
inverse-rule derivative map into the negative square of the actual Dext
operator. This is an algebra identity only; it assumes no derivative. -/
theorem actualCoordinateDextNegativeSquareOperatorIdentityMinimumV3_32
    (n : ℤ) (z : ℂ) :
    let E : Type := SectorSquare n →L[ℂ] SectorSquare n
    let D₀ : E := actualCoordinateCenterD0NamedFunctionMinimumV1_30 n
    let I : E := Ring.inverse (1 + (z - spectralCenter n) • D₀)
    (((-ContinuousLinearMap.mulLeftRight ℂ E I I).comp
      (ContinuousLinearMap.toSpanSingleton ℂ D₀)) <• D₀) =
      ContinuousLinearMap.toSpanSingleton ℂ
        (-((I.comp D₀).comp (I.comp D₀))) := by
  dsimp
  let E : Type := SectorSquare n →L[ℂ] SectorSquare n
  letI : NormedRing E := ContinuousLinearMap.toNormedRing
  letI : NonUnitalNormedRing E := NormedRing.toNonUnitalNormedRing
  letI : NormedAddCommGroup E := NonUnitalNormedRing.toNormedAddCommGroup
  letI : NormedAlgebra ℂ E := ContinuousLinearMap.toNormedAlgebra
  letI : NormedSpace ℂ E := ContinuousLinearMap.toNormedSpace
  let D₀ : E := actualCoordinateCenterD0NamedFunctionMinimumV1_30 n
  let I : E := Ring.inverse (1 + (z - spectralCenter n) • D₀)
  apply ContinuousLinearMap.ext
  intro δ
  apply ContinuousLinearMap.ext
  intro f
  simp only [_root_.smul_apply,
    MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op,
    ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.map_smul,
    smul_neg]

end NlsGge.Schur
