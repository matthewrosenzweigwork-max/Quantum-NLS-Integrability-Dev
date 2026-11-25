import NlsGge.Schur.ActualCoordinatePairConjugacyContinuousLinearMapDictionaryV1_27
import NlsGge.Schur.ActualCoordinatePairEndomorphismModuleCoherenceMinimumV1_28
import Mathlib.Algebra.Module.Defs
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.CStarAlgebra.Classes

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

private abbrev ActualCoordinateEndomorphismsForNormedCoherence28 (n : ℤ) :=
  SectorSquare n →L[ℂ] SectorSquare n

/-- The operator-NormedSpace scalar module used by `AnalyticOnNhd` on the
actual coordinate-endomorphism carrier agrees with the CStar module used by
the actual conjugacy CLM. The proof first identifies the operator action with
the ambient CLM action, then uses the already checked ambient/CStar equality.
This isolates the source-module dictionary required by the analytic
composition API; it makes no analyticity claim. -/
theorem actualCoordinateEndomorphismNormedModule_eq_cstarV1_28 (n : ℤ) :
    (ContinuousLinearMap.toNormedSpace :
      NormedSpace ℂ (ActualCoordinateEndomorphismsForNormedCoherence28 n)).toModule =
      (CStarAlgebra.toNonUnitalCStarAlgebra
        (ActualCoordinateEndomorphismsForNormedCoherence28 n)).toModule := by
  calc
    (ContinuousLinearMap.toNormedSpace :
      NormedSpace ℂ (ActualCoordinateEndomorphismsForNormedCoherence28 n)).toModule =
        (ContinuousLinearMap.module :
          Module ℂ (ActualCoordinateEndomorphismsForNormedCoherence28 n)) := by
            apply Module.ext'
            intro c T
            rfl
    _ = (CStarAlgebra.toNonUnitalCStarAlgebra
        (ActualCoordinateEndomorphismsForNormedCoherence28 n)).toModule :=
      actualCoordinateEndomorphismModule_eq_cstarV1_28 n

end NlsGge.Schur
