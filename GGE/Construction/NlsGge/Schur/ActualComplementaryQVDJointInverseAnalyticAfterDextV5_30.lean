import NlsGge.Schur.ActualParityPairPotentialParameterAfterScalarWrapper23
import NlsGge.Schur.FreeResolventComplementaryInverseOnRangeActual
import NlsGge.Schur.ActualComplementarySchurUnitAndAnalyticInverse23
import NlsGge.Schur.ActualCoordinateFreeResolventCenterInverseAnalyticPrerequisiteV1_26
import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30
import NlsGge.Schur.ActualQVDProductOperatorDictionaryMinimumV3_30
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Normed.Operator.Mul

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

local notation "H1PairQVD30" =>
  WeightedHilbert (sobolevModeWeight (1 : ℝ)) ×
    WeightedHilbert (sobolevModeWeight (1 : ℝ))

/-- The actual joint opposite complementary factor, using the total actual
radius-two free-resolvent family on the complex spectral coordinate and the
actual independent H¹-pair potential map on the second coordinate. -/
def actualComplementaryQVDJointParameterV5_30 (n : ℤ) :
    (ℂ × H1PairQVD30) → ParityPair n →L[ℂ] ParityPair n :=
  fun x =>
    (freeResolventComplementaryProjectionTransported n).comp
      ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n x.2).comp
        (actualFreeResolventCenterExtensionV1_30 n x.1))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- The concrete actual joint QVD inverse is analytic on the true spectral-disk
and independent two-field H¹ ball domain under the existing signed-index and
large-index hypotheses. -/
theorem analyticOnNhd_actualComplementaryQVDJointInverseAfterDextV5_30
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|) :
    AnalyticOnNhd ℂ
      (fun x : ℂ × H1PairQVD30 =>
        Ring.inverse
          (1 - actualComplementaryQVDJointParameterV5_30 n x))
      {x : ℂ × H1PairQVD30 |
        x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R} := by
  let S : Set (ℂ × H1PairQVD30) :=
    {x | x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R}
  let A : (ℂ × H1PairQVD30) → ParityPair n →L[ℂ] ParityPair n :=
    actualComplementaryQVDJointParameterV5_30 n
  let Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n
  let P : H1PairQVD30 →L[ℂ] (ParityPair n →L[ℂ] ParityPair n) :=
    actualParityPairPotentialParameterAfterScalarWrapperCLM23 n
  let D : ℂ → ParityPair n →L[ℂ] ParityPair n :=
    actualFreeResolventCenterExtensionV1_30 n
  have hD : AnalyticOnNhd ℂ D (Metric.ball (spectralCenter n) 2) := by
    exact actualFreeResolventCenterExtension_analyticOnNhdV1_30 n
  have hfst : AnalyticOnNhd ℂ (fun x : ℂ × H1PairQVD30 => x.1) S :=
    analyticOnNhd_fst
  have hfstMaps : Set.MapsTo
      (fun x : ℂ × H1PairQVD30 => x.1) S
      (Metric.ball (spectralCenter n) 2) := by
    intro x hx
    change x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R at hx
    rcases hx with ⟨hz, -, -⟩
    have hz : ‖x.1 - spectralCenter n‖ ≤ 1 := by
      change ‖x.1 - spectralCenter n‖ ≤ 1 at hz
      exact hz
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖x.1 - spectralCenter n‖ < 2
    linarith
  have hDpullCLM : AnalyticOnNhd ℂ (fun x : ℂ × H1PairQVD30 => D x.1) S :=
    hD.comp hfst hfstMaps
  have hsnd : AnalyticOnNhd ℂ (fun x : ℂ × H1PairQVD30 => x.2) S :=
    analyticOnNhd_snd
  have hsndMaps : Set.MapsTo
      (fun x : ℂ × H1PairQVD30 => x.2) S Set.univ := by
    intro x hx
    exact Set.mem_univ _
  have hPanalytic : AnalyticOnNhd ℂ (fun p : H1PairQVD30 => P p) Set.univ := by
    intro p hp
    simpa only using!
      (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := H1PairQVD30)
        (F := ParityPair n →L[ℂ] ParityPair n) P p)
  have hPpullCLM : AnalyticOnNhd ℂ (fun x : ℂ × H1PairQVD30 => P x.2) S := by
    exact hPanalytic.comp hsnd hsndMaps
  have hdict := actualQVDProductAnalyticTargetDictionaryMinimumV3_30 R n
  letI : NormedRing (ParityPair n →L[ℂ] ParityPair n) :=
    ContinuousLinearMap.toNormedRing
  letI : NonUnitalNormedRing (ParityPair n →L[ℂ] ParityPair n) :=
    NormedRing.toNonUnitalNormedRing
  letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : NormedAlgebra ℂ (ParityPair n →L[ℂ] ParityPair n) :=
    ContinuousLinearMap.toNormedAlgebra
  letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
    NormedAlgebra.toNormedSpace (ParityPair n →L[ℂ] ParityPair n)
  have hDpullRing : AnalyticOnNhd ℂ
      (fun x : ℂ × H1PairQVD30 => D x.1) S := by
    have hactual :
        (letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
          ContinuousLinearMap.toNormedAddCommGroup;
         letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
          ContinuousLinearMap.toNormedSpace;
         AnalyticOnNhd ℂ
        (fun x : ℂ × ActualH1PairQVDMinimumV3_30 =>
          actualFreeResolventCenterExtensionV1_30 n x.1)
        {x : ℂ × ActualH1PairQVDMinimumV3_30 |
          x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R}) := by
      simpa only [D] using hDpullCLM
    exact Eq.mp hdict.1 hactual
  have hPpullRing : AnalyticOnNhd ℂ
      (fun x : ℂ × H1PairQVD30 => P x.2) S := by
    have hactual :
        (letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
          ContinuousLinearMap.toNormedAddCommGroup;
         letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
          ContinuousLinearMap.toNormedSpace;
         AnalyticOnNhd ℂ
        (fun x : ℂ × ActualH1PairQVDMinimumV3_30 =>
          actualParityPairPotentialParameterAfterScalarWrapperCLM23 n x.2)
        {x : ℂ × ActualH1PairQVDMinimumV3_30 |
          x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R}) := by
      simpa only [P] using hPpullCLM
    exact Eq.mp hdict.2 hactual
  have hQ : AnalyticOnNhd ℂ (fun _ : ℂ × H1PairQVD30 => Q) S :=
    analyticOnNhd_const
  have hAanalytic : AnalyticOnNhd ℂ A S := by
    have hPD : AnalyticOnNhd ℂ
        (fun x : ℂ × H1PairQVD30 => P x.2 * D x.1) S := by
      intro x hx
      simpa only using! ((hPpullRing x hx).mul (hDpullRing x hx))
    have hproduct : AnalyticOnNhd ℂ
        (fun x : ℂ × H1PairQVD30 => Q * (P x.2 * D x.1)) S := by
      intro x hx
      simpa only using! ((hQ x hx).mul (hPD x hx))
    simpa only [A, Q, P, D, ContinuousLinearMap.mul_def] using! hproduct
  have hmaps : Set.MapsTo A S
      {T : ParityPair n →L[ℂ] ParityPair n | ‖T * T‖ ≤ (1 / 2 : ℝ)} := by
    intro x hx
    rcases x with ⟨z, p⟩
    change z ∈ spectralDisk n ∧ ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R at hx
    rcases hx with ⟨hz, hp₁, hp₂⟩
    let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
    let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
    let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
    let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
    have hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R := by
      rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
      exact hp₁
    have hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R := by
      rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
      exact hp₂
    have hsq := freeResolventComplementaryPotentialOpposite_square_norm_le_half_actual22
      u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz hlarge
    have hfactor : A (z, p) =
        freeResolventComplementaryPotentialOppositeFactor22
          u₁ u₂ hu₁ hu₂ n z hz := by
      dsimp [A, actualComplementaryQVDJointParameterV5_30,
        freeResolventComplementaryPotentialOppositeFactor22, u₁, u₂, hu₁, hu₂]
      rw [actualFreeResolventCenterExtension_eq_actualV1_30 n z hz]
      rw [actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply]
    change ‖A (z, p) * A (z, p)‖ ≤ (1 / 2 : ℝ)
    rw [hfactor]
    exact hsq
  have hinv :=
    (analyticOnNhd_ringInverse_one_sub_of_square_le_half23
      (E := ParityPair n)).comp hAanalytic hmaps
  have hfinalDict :
      (letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedAddCommGroup;
       letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedSpace;
       AnalyticOnNhd ℂ
        (fun x : ℂ × H1PairQVD30 => Ring.inverse (1 - A x)) S) =
      (letI : NormedRing (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedRing;
       letI : NonUnitalNormedRing (ParityPair n →L[ℂ] ParityPair n) :=
        NormedRing.toNonUnitalNormedRing;
       letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
        NonUnitalNormedRing.toNormedAddCommGroup;
       letI : NormedAlgebra ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedAlgebra;
       letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        NormedAlgebra.toNormedSpace (ParityPair n →L[ℂ] ParityPair n);
       AnalyticOnNhd ℂ
        (fun x : ℂ × H1PairQVD30 => Ring.inverse (1 - A x)) S) := by
    have hgroup := actualQVDPairEndNormedAddCommGroupDictionary_eqV3_30 n
    have hspace := actualQVDPairEndNormedSpaceDictionary_eqV3_30 n
    cases hgroup
    cases hspace
    rfl
  have hinvCLM := Eq.mpr hfinalDict hinv
  change AnalyticOnNhd ℂ
        (fun x : ℂ × H1PairQVD30 =>
      Ring.inverse
        (1 - actualComplementaryQVDJointParameterV5_30 n x))
    {x : ℂ × H1PairQVD30 |
      x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R}
  simpa only [S, A] using hinvCLM

end NlsGge.Schur
