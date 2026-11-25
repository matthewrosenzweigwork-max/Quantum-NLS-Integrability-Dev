import NlsGge.Schur.ActualPotentialTransposeEntryPrerequisites24
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

/-- Matrix-entry action of the actual square-coordinate conjugation, using the
checked PreLp single-coordinate evaluator. -/
theorem actualCoordinateConjugation24_single_matrix_entry_v2
    (n : ℤ) (i : Bool × Sector n) (y : SectorSquare n) :
    inner ℂ (lp.single 2 i (1 : ℂ)) (actualCoordinateConjugation23 n y) =
      inner ℂ y (lp.single 2 (!i.1, i.2) (1 : ℂ)) := by
  rw [actualPotentialTranspose_lp_single_inner_coordinate24,
    actualCoordinateConjugation23_apply, lp.inner_single_right]
  simp

/-- Matrix-entry action of the genuine coordinate transpose `C T† C` for an
arbitrary actual square-space CLM. -/
theorem actualCoordinateTranspose24_single_matrix_entry_v2
    (n : ℤ) (T : SectorSquare n →L[ℂ] SectorSquare n)
    (i j : Bool × Sector n) :
    inner ℂ (lp.single 2 i (1 : ℂ))
        (actualCoordinateTranspose23 n T (lp.single 2 j (1 : ℂ))) =
      inner ℂ (lp.single 2 (!j.1, j.2) (1 : ℂ))
        (T (lp.single 2 (!i.1, i.2) (1 : ℂ))) := by
  classical
  change inner ℂ (lp.single 2 i (1 : ℂ))
      (actualCoordinateConjugation23 n
        (T.adjoint (actualCoordinateConjugation23 n (lp.single 2 j (1 : ℂ))))) = _
  rw [actualCoordinateConjugation24_single_matrix_entry_v2,
    actualCoordinateConjugation23_single, T.adjoint_inner_left]

private def pairEndomorphismToSquareForTransposeEntryV2_24 (n : ℤ)
    (T : ParityPair n →L[ℂ] ParityPair n) : SectorSquare n →L[ℂ] SectorSquare n :=
  ((parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap).comp
    (T.comp
      ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap))

/-- Transport the coordinate transpose matrix entry to the genuine paired
Fourier basis. The PreLp coefficient evaluation is supplied by the passed
actual single-coordinate lemma on both conversion steps. -/
theorem actualPairTranspose24_single_matrix_entry_v2
    (n : ℤ) (T : ParityPair n →L[ℂ] ParityPair n)
    (i j : Bool × Sector n) :
    inner ℂ (parityPairVector n i)
        (actualPairTransposeAfterCoordinate23 n T (parityPairVector n j)) =
      inner ℂ (parityPairVector n (!j.1, j.2))
        (T (parityPairVector n (!i.1, i.2))) := by
  have hcoord : actualPairTransposeAfterCoordinate23 n T =
      ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap).comp
        ((actualCoordinateTranspose23 n
            (pairEndomorphismToSquareForTransposeEntryV2_24 n T)).comp
          ((parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap)) := rfl
  calc
    _ = inner ℂ (lp.single 2 i (1 : ℂ))
        (actualCoordinateTranspose23 n
          (pairEndomorphismToSquareForTransposeEntryV2_24 n T)
          (lp.single 2 j (1 : ℂ))) := by
      rw [← parityPairRepr_inner n
        (actualPairTransposeAfterCoordinate23 n T (parityPairVector n j)) i]
      rw [hcoord]
      simp [pairEndomorphismToSquareForTransposeEntryV2_24,
        ContinuousLinearMap.comp_apply, parityPairRepr_vector]
      simpa only using!
        (actualPotentialTranspose_lp_single_inner_coordinate24 n i
          (actualCoordinateTranspose23 n
            (pairEndomorphismToSquareForTransposeEntryV2_24 n T)
            (lp.single 2 j (1 : ℂ)))).symm
    _ = inner ℂ (lp.single 2 (!j.1, j.2) (1 : ℂ))
        (pairEndomorphismToSquareForTransposeEntryV2_24 n T
          (lp.single 2 (!i.1, i.2) (1 : ℂ))) :=
      actualCoordinateTranspose24_single_matrix_entry_v2 n _ i j
    _ = inner ℂ (parityPairVector n (!j.1, j.2))
        (T (parityPairVector n (!i.1, i.2))) := by
      rw [← parityPairRepr_inner n
        (T (parityPairVector n (!i.1, i.2))) (!j.1, j.2)]
      simp [pairEndomorphismToSquareForTransposeEntryV2_24,
        ContinuousLinearMap.comp_apply]
      rw [actualPotentialTranspose_repr_symm_single24]
      simpa only using!
        actualPotentialTranspose_lp_single_inner_coordinate24 n
          (!j.1, j.2) (parityPairRepr n (T (parityPairVector n (!i.1, i.2))))

end NlsGge.Schur
