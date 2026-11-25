import NlsGge.Schur.ActualComplementaryQVDJointInverseAnalyticAfterDextV5_30
import NlsGge.Schur.ActualQVDProductOperatorDictionaryMinimumV3_30
import NlsGge.Schur.ActualParityPairPotentialParameterAfterScalarWrapper23
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Normed.Operator.Mul

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

abbrev ActualSchurEffectiveH1PairV3_30 := ActualH1PairQVDMinimumV3_30

/-- The actual source-order Schur operator, built from the radius-two Dext
family and the total actual joint complementary inverse. -/
def actualSchurEffectiveOperatorAfterDextV3_30 (n : ℤ)
    (x : ℂ × ActualSchurEffectiveH1PairV3_30) : ParityPair n →L[ℂ] ParityPair n :=
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  let V : ParityPair n →L[ℂ] ParityPair n :=
    actualParityPairPotentialParameterAfterScalarWrapperCLM23 n x.2
  let D : ParityPair n →L[ℂ] ParityPair n :=
    actualFreeResolventCenterExtensionV1_30 n x.1
  let S : ParityPair n →L[ℂ] ParityPair n :=
    Ring.inverse (1 - actualComplementaryQVDJointParameterV5_30 n x)
  P.comp (V.comp P) + P.comp (V.comp ((D.comp S).comp (V.comp P)))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- The concrete effective Schur operator in the manuscript's order is jointly
analytic in the spectral parameter and independent complex H¹ pair on the
actual disk-times-product-ball domain. -/
theorem analyticOnNhd_actualSchurEffectiveOperatorAfterDextV3_30
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|) :
    AnalyticOnNhd ℂ
      (actualSchurEffectiveOperatorAfterDextV3_30 n)
      {x : ℂ × ActualSchurEffectiveH1PairV3_30 |
        x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R} := by
  let Sdom : Set (ℂ × ActualSchurEffectiveH1PairV3_30) :=
    {x | x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R}
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  let V : ActualSchurEffectiveH1PairV3_30 →L[ℂ]
      (ParityPair n →L[ℂ] ParityPair n) :=
    actualParityPairPotentialParameterAfterScalarWrapperCLM23 n
  let D : ℂ → ParityPair n →L[ℂ] ParityPair n :=
    actualFreeResolventCenterExtensionV1_30 n
  let S : (ℂ × ActualSchurEffectiveH1PairV3_30) → ParityPair n →L[ℂ] ParityPair n :=
    fun x => Ring.inverse (1 - actualComplementaryQVDJointParameterV5_30 n x)

  have hDbase : AnalyticOnNhd ℂ D (Metric.ball (spectralCenter n) 2) := by
    exact actualFreeResolventCenterExtension_analyticOnNhdV1_30 n
  have hfst : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => x.1) Sdom :=
    analyticOnNhd_fst
  have hfstMaps : Set.MapsTo
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => x.1) Sdom
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
  have hDclm : AnalyticOnNhd ℂ (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => D x.1) Sdom :=
    hDbase.comp hfst hfstMaps

  have hsnd : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => x.2) Sdom :=
    analyticOnNhd_snd
  have hsndMaps : Set.MapsTo
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => x.2) Sdom Set.univ := by
    intro x hx
    exact Set.mem_univ _
  have hVbase : AnalyticOnNhd ℂ (fun p : ActualSchurEffectiveH1PairV3_30 => V p) Set.univ := by
    intro p hp
    simpa only using!
      (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
        (E := ActualSchurEffectiveH1PairV3_30)
        (F := ParityPair n →L[ℂ] ParityPair n) V p)
  have hVclm : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => V x.2) Sdom :=
    hVbase.comp hsnd hsndMaps

  have hSclm : AnalyticOnNhd ℂ S Sdom := by
    simpa only [S] using
      (analyticOnNhd_actualComplementaryQVDJointInverseAfterDextV5_30
        R hR n hn hlarge)

  have hDictFactors := actualQVDProductAnalyticTargetDictionaryMinimumV3_30 R n
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

  have hDring : AnalyticOnNhd ℂ (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => D x.1) Sdom := by
    have hactual :
        (letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
          ContinuousLinearMap.toNormedAddCommGroup;
         letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
          ContinuousLinearMap.toNormedSpace;
         AnalyticOnNhd ℂ
          (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => D x.1) Sdom) := by
      exact hDclm
    exact Eq.mp hDictFactors.1 hactual
  have hVring : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => V x.2) Sdom := by
    have hactual :
        (letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
          ContinuousLinearMap.toNormedAddCommGroup;
         letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
          ContinuousLinearMap.toNormedSpace;
         AnalyticOnNhd ℂ
          (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => V x.2) Sdom) := by
      exact hVclm
    exact Eq.mp hDictFactors.2 hactual

  have hSdict :
      (letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedAddCommGroup;
       letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedSpace;
       AnalyticOnNhd ℂ S Sdom) =
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
       AnalyticOnNhd ℂ S Sdom) := by
    have hgroup := actualQVDPairEndNormedAddCommGroupDictionary_eqV3_30 n
    have hspace := actualQVDPairEndNormedSpaceDictionary_eqV3_30 n
    cases hgroup
    cases hspace
    rfl
  have hSring : AnalyticOnNhd ℂ S Sdom := Eq.mp hSdict hSclm

  have hPconst : AnalyticOnNhd ℂ (fun _ : ℂ × ActualSchurEffectiveH1PairV3_30 => P) Sdom :=
    analyticOnNhd_const
  have hVP : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => V x.2 * P) Sdom := by
    intro x hx
    simpa only using! (hVring x hx).mul (hPconst x hx)
  have hPVP : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => P * (V x.2 * P)) Sdom := by
    intro x hx
    simpa only using! (hPconst x hx).mul (hVP x hx)
  have hDS : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => D x.1 * S x) Sdom := by
    intro x hx
    simpa only using! (hDring x hx).mul (hSring x hx)
  have hDSVP : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 =>
        (D x.1 * S x) * (V x.2 * P)) Sdom := by
    intro x hx
    simpa only using! (hDS x hx).mul (hVP x hx)
  have hVDSVP : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 =>
        V x.2 * ((D x.1 * S x) * (V x.2 * P))) Sdom := by
    intro x hx
    simpa only using! (hVring x hx).mul (hDSVP x hx)
  have hsecond : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 =>
        P * (V x.2 * ((D x.1 * S x) * (V x.2 * P)))) Sdom := by
    intro x hx
    simpa only using! (hPconst x hx).mul (hVDSVP x hx)
  have hsum : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 =>
        P * (V x.2 * P) + P * (V x.2 * ((D x.1 * S x) * (V x.2 * P)))) Sdom := by
    exact hPVP.add hsecond

  have hsumCLMdict :
      (letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedAddCommGroup;
       letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedSpace;
       AnalyticOnNhd ℂ
        (actualSchurEffectiveOperatorAfterDextV3_30 n) Sdom) =
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
        (actualSchurEffectiveOperatorAfterDextV3_30 n) Sdom) := by
    have hgroup := actualQVDPairEndNormedAddCommGroupDictionary_eqV3_30 n
    have hspace := actualQVDPairEndNormedSpaceDictionary_eqV3_30 n
    cases hgroup
    cases hspace
    rfl
  have hsumCanonical :
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
        (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 =>
          P * (V x.2 * P) + P * (V x.2 * ((D x.1 * S x) * (V x.2 * P)))) Sdom) := by
    have hgroup := actualQVDPairEndNormedAddCommGroupDictionary_eqV3_30 n
    have hspace := actualQVDPairEndNormedSpaceDictionary_eqV3_30 n
    cases hgroup
    cases hspace
    exact hsum
  have hMring :
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
        (actualSchurEffectiveOperatorAfterDextV3_30 n) Sdom) := by
    simpa only [actualSchurEffectiveOperatorAfterDextV3_30,
      ContinuousLinearMap.mul_def, S, V, D] using! hsumCanonical
  have hMclm := Eq.mpr hsumCLMdict hMring
  simpa only [Sdom] using hMclm

end NlsGge.Schur
