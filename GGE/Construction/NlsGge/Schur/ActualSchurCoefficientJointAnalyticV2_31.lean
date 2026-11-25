import NlsGge.Schur.ActualSchurEffectiveJointAnalyticAfterDextV3_30
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis

namespace NlsGge.Schur

/-- The actual bounded matrix-entry functional on the concrete parity-pair
endomorphism space. The convention is row `i`, column `j`:
`⟪e_i, T e_j⟫`. -/
def actualSchurEntryFunctional31 (n : ℤ) (i j : Bool × Sector n) :
    (ParityPair n →L[ℂ] ParityPair n) →L[ℂ] ℂ :=
  (innerSL ℂ (parityPairVector n i)).comp
    (ContinuousLinearMap.apply ℂ (ParityPair n) (parityPairVector n j))

/-- A concrete scalar entry of the paper-order Schur operator, with the actual
radius-two Dext and actual joint complementary inverse from batch 30. -/
def actualSchurCoefficientAfterDext31 (n : ℤ) (i j : Bool × Sector n)
    (x : ℂ × ActualSchurEffectiveH1PairV3_30) : ℂ :=
  actualSchurEntryFunctional31 n i j
    (actualSchurEffectiveOperatorAfterDextV3_30 n x)

/-- Each of the four actual resonant Schur coefficients is jointly analytic on
the original spectral disk times the two independent complex H¹ balls. The
statement only extracts entries from the checked operator-valued analyticity;
it adds no coefficient, center, or root analyticity premise. -/
theorem actualSchurCoefficientsJointAnalyticV2_31
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|) :
    let S : Set (ℂ × ActualSchurEffectiveH1PairV3_30) :=
      {x | x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R}
    AnalyticOnNhd ℂ
      (actualSchurCoefficientAfterDext31 n
        (true, resonantIndex n) (true, resonantIndex n)) S ∧
    AnalyticOnNhd ℂ
      (actualSchurCoefficientAfterDext31 n
        (true, resonantIndex n) (false, resonantIndex n)) S ∧
    AnalyticOnNhd ℂ
      (actualSchurCoefficientAfterDext31 n
        (false, resonantIndex n) (true, resonantIndex n)) S ∧
    AnalyticOnNhd ℂ
      (actualSchurCoefficientAfterDext31 n
        (false, resonantIndex n) (false, resonantIndex n)) S := by
  dsimp only [actualSchurCoefficientAfterDext31]
  let S : Set (ℂ × ActualSchurEffectiveH1PairV3_30) :=
    {x | x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R}
  have hM := analyticOnNhd_actualSchurEffectiveOperatorAfterDextV3_30
    R hR n hn hlarge
  have entryAnalytic (i j : Bool × Sector n) :
      AnalyticOnNhd ℂ
        (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 =>
          actualSchurEntryFunctional31 n i j
            (actualSchurEffectiveOperatorAfterDextV3_30 n x)) S := by
    exact (actualSchurEntryFunctional31 n i j).comp_analyticOnNhd hM
  exact ⟨entryAnalytic _ _, entryAnalytic _ _,
    entryAnalytic _ _, entryAnalytic _ _⟩

end NlsGge.Schur
