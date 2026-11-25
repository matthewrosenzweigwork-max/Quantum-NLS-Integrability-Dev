import NlsGge.Schur.ActualCoordinateFreeResolventCenterInverseAnalyticPrerequisiteV1_26
import NlsGge.Schur.ActualCoordinateEndomorphismNormedModuleCoherenceMinimumV1_28
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Analytic.Basic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

private abbrev ActualCoordinateEndomorphismsForTransport29 (n : ℤ) :=
  SectorSquare n →L[ℂ] SectorSquare n

private abbrev ActualPairEndomorphismsForTransport29 (n : ℤ) :=
  ParityPair n →L[ℂ] ParityPair n

/-- The already checked operator/CStar module equality induces equality of the
full NormedSpace dictionaries. This lemma isolates dictionary identity only;
it makes no claim about an analytic function. -/
theorem actualCoordinateEndomorphismNormedSpace_eq_cstarMinimumV3_29
    (n : ℤ) :
    (ContinuousLinearMap.toNormedSpace :
      NormedSpace ℂ (ActualCoordinateEndomorphismsForTransport29 n)) =
    (CStarAlgebra.toNonUnitalCStarAlgebra
      (ActualCoordinateEndomorphismsForTransport29 n)).toNormedSpace := by
  have hmodule := actualCoordinateEndomorphismNormedModule_eq_cstarV1_28 n
  cases hmodule
  rfl

/-- An analytic proposition can be transported along the actual checked
NormedSpace-dictionary equality by an explicit dependent motive. -/
theorem actualCoordinateAnalyticDictionaryCastMinimumV3_29
    (n : ℤ) (f : ℂ → ActualCoordinateEndomorphismsForTransport29 n)
    (s : Set ℂ)
    (hf : (letI : NormedSpace ℂ (ActualCoordinateEndomorphismsForTransport29 n) :=
      (CStarAlgebra.toNonUnitalCStarAlgebra
        (ActualCoordinateEndomorphismsForTransport29 n)).toNormedSpace;
      AnalyticOnNhd ℂ f s)) :
    (letI : NormedSpace ℂ (ActualCoordinateEndomorphismsForTransport29 n) :=
      ContinuousLinearMap.toNormedSpace;
      AnalyticOnNhd ℂ f s) := by
  have hprop :
      (letI : NormedSpace ℂ (ActualCoordinateEndomorphismsForTransport29 n) :=
        (CStarAlgebra.toNonUnitalCStarAlgebra
          (ActualCoordinateEndomorphismsForTransport29 n)).toNormedSpace;
        AnalyticOnNhd ℂ f s) =
      (letI : NormedSpace ℂ (ActualCoordinateEndomorphismsForTransport29 n) :=
        ContinuousLinearMap.toNormedSpace;
        AnalyticOnNhd ℂ f s) := by
    exact congrArg
      (fun ns : NormedSpace ℂ (ActualCoordinateEndomorphismsForTransport29 n) =>
        (letI : NormedSpace ℂ (ActualCoordinateEndomorphismsForTransport29 n) := ns;
        AnalyticOnNhd ℂ f s))
      (actualCoordinateEndomorphismNormedSpace_eq_cstarMinimumV3_29 n)
  exact hprop.mp hf

/-- The paired operator CLM's concrete operator norm is invariant under its
actual negation. This isolates the norm identity needed by the Neumann-unit
bound under the explicit operator-NormedSpace dictionary. -/
theorem actualPairEndomorphism_norm_negMinimumV3_29
    (n : ℤ) (T : ActualPairEndomorphismsForTransport29 n) :
    ‖-T‖ = ‖T‖ := by
  exact norm_neg T

/-- In the actual paired endomorphism ring, the element used by
`IsUnit.one_sub_of_norm_lt_one` is exactly the `1 + T` factor. -/
theorem actualPairEndomorphism_one_sub_negMinimumV3_29
    (n : ℤ) (T : ActualPairEndomorphismsForTransport29 n) :
    (1 - -T) = 1 + T := by
  apply ContinuousLinearMap.ext
  intro x
  change x - -(T x) = x + T x
  exact sub_neg_eq_add x (T x)

/-- Unit status transports across the preceding concrete CLM equality. -/
theorem actualPairEndomorphism_isUnit_one_add_of_sub_negMinimumV3_29
    (n : ℤ) (T : ActualPairEndomorphismsForTransport29 n)
    (h : IsUnit (1 - -T)) : IsUnit (1 + T) := by
  exact (actualPairEndomorphism_one_sub_negMinimumV3_29 n T) ▸ h

end NlsGge.Schur
