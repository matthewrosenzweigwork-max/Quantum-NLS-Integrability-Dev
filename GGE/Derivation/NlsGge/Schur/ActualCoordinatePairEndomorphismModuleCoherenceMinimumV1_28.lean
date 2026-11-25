import NlsGge.Schur.ActualCoordinatePairConjugacyContinuousLinearMapDictionaryV1_27
import Mathlib.Algebra.Module.Defs
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.CStarAlgebra.Classes

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

private abbrev ActualCoordinateEndomorphisms28 (n : ℤ) :=
  SectorSquare n →L[ℂ] SectorSquare n

private abbrev ActualPairEndomorphisms28 (n : ℤ) :=
  ParityPair n →L[ℂ] ParityPair n

/-- The ambient pointwise CLM scalar action on the actual coordinate
endomorphism carrier agrees with its CStar-algebra scalar action. This is the
source-module equality needed to compare the already elaborated analytic
family with a CStar-typed outer conjugacy map. -/
theorem actualCoordinateEndomorphismModule_eq_cstarV1_28 (n : ℤ) :
    (ContinuousLinearMap.module :
      Module ℂ (ActualCoordinateEndomorphisms28 n)) =
      (CStarAlgebra.toNonUnitalCStarAlgebra
        (ActualCoordinateEndomorphisms28 n)).toModule := by
  apply Module.ext'
  intro c T
  ext x
  simp [Algebra.smul_def]

/-- The ambient CLM target module and the module carried by the actual
operator NormedSpace structure have the same scalar action. -/
theorem actualPairEndomorphismModule_eq_normedV1_28 (n : ℤ) :
    (ContinuousLinearMap.module :
      Module ℂ (ActualPairEndomorphisms28 n)) =
      (ContinuousLinearMap.toNormedSpace :
        NormedSpace ℂ (ActualPairEndomorphisms28 n)).toModule := by
  apply Module.ext'
  intro c T
  rfl

end NlsGge.Schur
