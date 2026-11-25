import NlsGge.Schur.ActualPairTransposeTransportAfterCoordinatePrerequisite23
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open scoped InnerProduct

private theorem actualCoordinateTranspose23_add_prerequisiteV2_25
    (n : ℤ) (T S : SectorSquare n →L[ℂ] SectorSquare n) :
    actualCoordinateTranspose23 n (T + S) =
      actualCoordinateTranspose23 n T + actualCoordinateTranspose23 n S := by
  ext x i
  simp [actualCoordinateTranspose23, actualCoordinateConjugation23_apply,
    ContinuousLinearMap.adjoint.map_add]

private theorem actualCoordinateTranspose23_sub_prerequisiteV2_25
    (n : ℤ) (T S : SectorSquare n →L[ℂ] SectorSquare n) :
    actualCoordinateTranspose23 n (T - S) =
      actualCoordinateTranspose23 n T - actualCoordinateTranspose23 n S := by
  ext x i
  simp [actualCoordinateTranspose23, actualCoordinateConjugation23_apply,
    ContinuousLinearMap.adjoint.map_sub]

theorem actualPairTransposeAfterCoordinate23_add_prerequisiteV2_25
    (n : ℤ) (T S : ParityPair n →L[ℂ] ParityPair n) :
    actualPairTransposeAfterCoordinate23 n (T + S) =
      actualPairTransposeAfterCoordinate23 n T +
        actualPairTransposeAfterCoordinate23 n S := by
  let Ec : ParityPair n →L[ℂ] SectorSquare n :=
    (parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap
  let Es : SectorSquare n →L[ℂ] ParityPair n :=
    (parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap
  have htransport : Ec.comp ((T + S).comp Es) =
      Ec.comp (T.comp Es) + Ec.comp (S.comp Es) := by
    apply ContinuousLinearMap.ext
    intro x
    change Ec ((T + S) (Es x)) = Ec (T (Es x)) + Ec (S (Es x))
    rw [ContinuousLinearMap.add_apply, map_add]
  change Es.comp
      ((actualCoordinateTranspose23 n
          (Ec.comp ((T + S).comp Es))).comp Ec) =
    Es.comp ((actualCoordinateTranspose23 n (Ec.comp (T.comp Es))).comp Ec) +
      Es.comp ((actualCoordinateTranspose23 n (Ec.comp (S.comp Es))).comp Ec)
  rw [htransport, actualCoordinateTranspose23_add_prerequisiteV2_25]
  apply ContinuousLinearMap.ext
  intro x
  change Es
      ((actualCoordinateTranspose23 n (Ec.comp (T.comp Es))) (Ec x) +
        (actualCoordinateTranspose23 n (Ec.comp (S.comp Es))) (Ec x)) =
    Es ((actualCoordinateTranspose23 n (Ec.comp (T.comp Es))) (Ec x)) +
      Es ((actualCoordinateTranspose23 n (Ec.comp (S.comp Es))) (Ec x))
  exact map_add Es _ _

theorem actualPairTransposeAfterCoordinate23_sub_prerequisiteV2_25
    (n : ℤ) (T S : ParityPair n →L[ℂ] ParityPair n) :
    actualPairTransposeAfterCoordinate23 n (T - S) =
      actualPairTransposeAfterCoordinate23 n T -
        actualPairTransposeAfterCoordinate23 n S := by
  let Ec : ParityPair n →L[ℂ] SectorSquare n :=
    (parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap
  let Es : SectorSquare n →L[ℂ] ParityPair n :=
    (parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap
  have htransport : Ec.comp ((T - S).comp Es) =
      Ec.comp (T.comp Es) - Ec.comp (S.comp Es) := by
    apply ContinuousLinearMap.ext
    intro x
    change Ec ((T - S) (Es x)) = Ec (T (Es x)) - Ec (S (Es x))
    rw [ContinuousLinearMap.sub_apply, map_sub]
  change Es.comp
      ((actualCoordinateTranspose23 n
          (Ec.comp ((T - S).comp Es))).comp Ec) =
    Es.comp ((actualCoordinateTranspose23 n (Ec.comp (T.comp Es))).comp Ec) -
      Es.comp ((actualCoordinateTranspose23 n (Ec.comp (S.comp Es))).comp Ec)
  rw [htransport, actualCoordinateTranspose23_sub_prerequisiteV2_25]
  apply ContinuousLinearMap.ext
  intro x
  change Es
      ((actualCoordinateTranspose23 n (Ec.comp (T.comp Es))) (Ec x) -
        (actualCoordinateTranspose23 n (Ec.comp (S.comp Es))) (Ec x)) =
    Es ((actualCoordinateTranspose23 n (Ec.comp (T.comp Es))) (Ec x)) -
      Es ((actualCoordinateTranspose23 n (Ec.comp (S.comp Es))) (Ec x))
  exact map_sub Es _ _

end NlsGge.Schur
