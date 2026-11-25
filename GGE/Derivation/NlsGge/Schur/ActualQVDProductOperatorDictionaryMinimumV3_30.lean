import NlsGge.Schur.ActualCoordinatePairEndomorphismModuleCoherenceMinimumV1_28
import NlsGge.Schur.ActualParityPairPotentialParameterAfterScalarWrapper23
import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30
import Mathlib.Analysis.Normed.Operator.Mul

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

/-- The exact actual independent pair of complex H¹ weighted carriers used by
the joint Schur parameter map. -/
abbrev ActualH1PairQVDMinimumV3_30 :=
  WeightedHilbert (sobolevModeWeight (1 : ℝ)) ×
    WeightedHilbert (sobolevModeWeight (1 : ℝ))

/-- The exact actual paired endomorphism carrier. -/
abbrev ActualPairEndQVDMinimumV3_30 (n : ℤ) :=
  ParityPair n →L[ℂ] ParityPair n

/-- The CLM and operator-ring normed additive-group structures coincide on
the actual paired endomorphism carrier. -/
theorem actualQVDPairEndNormedAddCommGroupDictionary_eqV3_30 (n : ℤ) :
    (ContinuousLinearMap.toNormedAddCommGroup :
      NormedAddCommGroup (ActualPairEndQVDMinimumV3_30 n)) =
    (NonUnitalNormedRing.toNormedAddCommGroup :
      NormedAddCommGroup (ActualPairEndQVDMinimumV3_30 n)) := by
  letI : NormedRing (ActualPairEndQVDMinimumV3_30 n) := ContinuousLinearMap.toNormedRing
  letI : NonUnitalNormedRing (ActualPairEndQVDMinimumV3_30 n) :=
    NormedRing.toNonUnitalNormedRing
  rfl

/-- The CLM and normed-algebra scalar actions on actual paired endomorphisms
coincide. The explicit `toNormedSpace` argument is the operator carrier: the
pinned declaration takes its algebra carrier first, not the scalar field. -/
theorem actualQVDPairEndNormedSpaceDictionary_eqV3_30 (n : ℤ) :
    (letI : NormedAddCommGroup (ActualPairEndQVDMinimumV3_30 n) :=
      ContinuousLinearMap.toNormedAddCommGroup;
      (ContinuousLinearMap.toNormedSpace :
        NormedSpace ℂ (ActualPairEndQVDMinimumV3_30 n))) =
    (letI : NormedAddCommGroup (ActualPairEndQVDMinimumV3_30 n) :=
      ContinuousLinearMap.toNormedAddCommGroup;
      (NormedAlgebra.toNormedSpace (ActualPairEndQVDMinimumV3_30 n) :
        NormedSpace ℂ (ActualPairEndQVDMinimumV3_30 n))) := by
  letI : NormedAddCommGroup (ActualPairEndQVDMinimumV3_30 n) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedRing (ActualPairEndQVDMinimumV3_30 n) := ContinuousLinearMap.toNormedRing
  letI : NormedAlgebra ℂ (ActualPairEndQVDMinimumV3_30 n) :=
    ContinuousLinearMap.toNormedAlgebra
  apply NormedSpace.ext
  funext c T
  rfl

/-- Convert only the output dictionaries for the two actual factors used in
the joint QVD product. Both predicates keep the true complex-disk × two
independent H¹-ball domain; no analytic conclusion is assumed here. -/
theorem actualQVDProductAnalyticTargetDictionaryMinimumV3_30
    (R : ℝ) (n : ℤ) :
    (letI : NormedAddCommGroup (ActualPairEndQVDMinimumV3_30 n) :=
      ContinuousLinearMap.toNormedAddCommGroup;
      letI : NormedSpace ℂ (ActualPairEndQVDMinimumV3_30 n) :=
        ContinuousLinearMap.toNormedSpace;
      AnalyticOnNhd ℂ
        (fun x : ℂ × ActualH1PairQVDMinimumV3_30 =>
          actualFreeResolventCenterExtensionV1_30 n x.1)
        {x : ℂ × ActualH1PairQVDMinimumV3_30 |
          x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R}) =
    (letI : NormedRing (ActualPairEndQVDMinimumV3_30 n) :=
      ContinuousLinearMap.toNormedRing;
      letI : NonUnitalNormedRing (ActualPairEndQVDMinimumV3_30 n) :=
        NormedRing.toNonUnitalNormedRing;
      letI : NormedAlgebra ℂ (ActualPairEndQVDMinimumV3_30 n) :=
        ContinuousLinearMap.toNormedAlgebra;
      AnalyticOnNhd ℂ
        (fun x : ℂ × ActualH1PairQVDMinimumV3_30 =>
          actualFreeResolventCenterExtensionV1_30 n x.1)
        {x : ℂ × ActualH1PairQVDMinimumV3_30 |
          x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R}) ∧
    ((letI : NormedAddCommGroup (ActualPairEndQVDMinimumV3_30 n) :=
      ContinuousLinearMap.toNormedAddCommGroup;
      letI : NormedSpace ℂ (ActualPairEndQVDMinimumV3_30 n) :=
        ContinuousLinearMap.toNormedSpace;
      AnalyticOnNhd ℂ
        (fun x : ℂ × ActualH1PairQVDMinimumV3_30 =>
          actualParityPairPotentialParameterAfterScalarWrapperCLM23 n x.2)
        {x : ℂ × ActualH1PairQVDMinimumV3_30 |
          x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R}) =
    (letI : NormedRing (ActualPairEndQVDMinimumV3_30 n) :=
      ContinuousLinearMap.toNormedRing;
      letI : NonUnitalNormedRing (ActualPairEndQVDMinimumV3_30 n) :=
        NormedRing.toNonUnitalNormedRing;
      letI : NormedAlgebra ℂ (ActualPairEndQVDMinimumV3_30 n) :=
        ContinuousLinearMap.toNormedAlgebra;
      AnalyticOnNhd ℂ
        (fun x : ℂ × ActualH1PairQVDMinimumV3_30 =>
          actualParityPairPotentialParameterAfterScalarWrapperCLM23 n x.2)
        {x : ℂ × ActualH1PairQVDMinimumV3_30 |
          x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R})) := by
  constructor
  · letI : NormedRing (ActualPairEndQVDMinimumV3_30 n) :=
      ContinuousLinearMap.toNormedRing
    letI : NonUnitalNormedRing (ActualPairEndQVDMinimumV3_30 n) :=
      NormedRing.toNonUnitalNormedRing
    letI : NormedAlgebra ℂ (ActualPairEndQVDMinimumV3_30 n) :=
      ContinuousLinearMap.toNormedAlgebra
    have hgroup := actualQVDPairEndNormedAddCommGroupDictionary_eqV3_30 n
    have hspace := actualQVDPairEndNormedSpaceDictionary_eqV3_30 n
    cases hgroup
    cases hspace
    rfl
  · letI : NormedRing (ActualPairEndQVDMinimumV3_30 n) :=
      ContinuousLinearMap.toNormedRing
    letI : NonUnitalNormedRing (ActualPairEndQVDMinimumV3_30 n) :=
      NormedRing.toNonUnitalNormedRing
    letI : NormedAlgebra ℂ (ActualPairEndQVDMinimumV3_30 n) :=
      ContinuousLinearMap.toNormedAlgebra
    have hgroup := actualQVDPairEndNormedAddCommGroupDictionary_eqV3_30 n
    have hspace := actualQVDPairEndNormedSpaceDictionary_eqV3_30 n
    cases hgroup
    cases hspace
    rfl

end NlsGge.Schur
