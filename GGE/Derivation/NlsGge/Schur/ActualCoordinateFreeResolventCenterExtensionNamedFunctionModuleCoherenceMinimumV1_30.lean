import NlsGge.Schur.ActualCoordinateEndomorphismNormedModuleCoherenceMinimumV1_28
import NlsGge.Schur.ActualCoordinateFreeResolventCenterInverseAnalyticPrerequisiteV1_26
import NlsGge.Schur.ActualFreeResolventCenterParityPairNormAfterSquareV2_24
import NlsGge.Schur.ActualCoordinatePairEndomorphismModuleCoherenceMinimumV1_28
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.CStarAlgebra.Classes

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The actual fixed coordinate free-resolvent at its signed spectral center,
written on the complete coordinate carrier. -/
def actualCoordinateCenterD0NamedFunctionMinimumV1_30 (n : ℤ) :
    SectorSquare n →L[ℂ] SectorSquare n :=
  freeResolventSquare n (spectralCenter n)
    (spectralCenter_mem_spectralDisk_scalarV2_24 n)

/-- The named total actual coordinate free-resolvent family used by the
radius-two construction. This is the concrete inverse-times-center formula,
not an abstract family or a family with an analytic assumption. -/
def actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30
    (n : ℤ) (z : ℂ) : SectorSquare n →L[ℂ] SectorSquare n :=
  Ring.inverse
    (1 + (z - spectralCenter n) • actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) *
    actualCoordinateCenterD0NamedFunctionMinimumV1_30 n

/-- The scalar-module dictionary used by the analytic postcomposition domain
and the ambient CLM scalar-module dictionary agree on the full coordinate
endomorphism carrier. -/
theorem actualCoordinateOperatorModule_eq_ambientModuleNamedFunctionMinimumV1_30
    (n : ℤ) :
    (ContinuousLinearMap.toNormedSpace :
      NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n)).toModule =
      ContinuousLinearMap.module := by
  calc
    (ContinuousLinearMap.toNormedSpace :
      NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n)).toModule =
        (CStarAlgebra.toNonUnitalCStarAlgebra
          (SectorSquare n →L[ℂ] SectorSquare n)).toModule :=
      actualCoordinateEndomorphismNormedModule_eq_cstarV1_28 n
    _ = ContinuousLinearMap.module :=
      (actualCoordinateEndomorphismModule_eq_cstarV1_28 n).symm

/-- Exact function-level bridge from the analytic theorem's operator-module
expression to the named concrete Dext family. The equality is obtained solely
by transporting the scalar-module dictionary already proved for this actual
CLM carrier. -/
theorem actualCoordinateFreeResolventCenterExtension_functionModuleCoherenceMinimumV1_30
    (n : ℤ) :
    (letI : Module ℂ (SectorSquare n →L[ℂ] SectorSquare n) :=
      (ContinuousLinearMap.toNormedSpace :
        NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n)).toModule;
      fun z : ℂ =>
        Ring.inverse
          (1 + (z - spectralCenter n) •
            actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) *
          actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) =
      actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30 n := by
  have hmodule :=
    actualCoordinateOperatorModule_eq_ambientModuleNamedFunctionMinimumV1_30 n
  cases hmodule
  rfl

end NlsGge.Schur
