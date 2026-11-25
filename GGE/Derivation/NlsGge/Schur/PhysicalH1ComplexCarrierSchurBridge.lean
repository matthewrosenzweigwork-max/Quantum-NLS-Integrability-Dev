import NlsGge.Hierarchy.RiccatiPhysicalH1CarrierAfterUnweightedCoordinateSecond
import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Hierarchy.RiccatiPhysicalFourierL2SymmCoefficientsSecond
import NlsGge.Analysis.PhysicalH1Bounds

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

open NlsGge.Pilot NlsGge.Analysis

local notation "H1Weight22" => sobolevModeWeight (1 : ℝ)
local instance : Fact (∀ n : ℤ, 0 < (1 : ℝ)) := ⟨by norm_num⟩

private theorem h1Weight22_ge_one (n : ℤ) : (1 : ℝ) ≤ H1Weight22 n := by
  change 1 ≤ Real.rpow (japaneseBracket n) (2 * (1 : ℝ))
  rw [NlsGge.Analysis.japaneseBracket_h1_weight]
  nlinarith [sq_nonneg (n : ℝ)]

/-- The genuine complex H¹ Fourier carrier embeds continuously and complex
linearly into the actual physical L² carrier. This is the complex structure
underlying the accepted real Sobolev carrier, with no proof-valued H¹ parameter. -/
def physicalH1ComplexCarrierToL2Actual22 :
    WeightedHilbert H1Weight22 →L[ℂ] PhysicalL2 := by
  let C : WeightedHilbert H1Weight22 →L[ℂ]
      WeightedHilbert (fun _ : ℤ => (1 : ℝ)) :=
    weightedComparisonContinuous H1Weight22 (fun _ : ℤ => (1 : ℝ)) 1
      (by norm_num) (fun n => by simpa only [one_mul] using h1Weight22_ge_one n)
  let U : WeightedHilbert (fun _ : ℤ => (1 : ℝ)) ≃ₗᵢ[ℂ]
      lp (fun _ : ℤ => ℂ) 2 := weightedIsometry (fun _ : ℤ => (1 : ℝ))
  let Uclm : WeightedHilbert (fun _ : ℤ => (1 : ℝ)) →L[ℂ]
      lp (fun _ : ℤ => ℂ) 2 := U.toContinuousLinearEquiv.toContinuousLinearMap
  let F : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] PhysicalL2 :=
    physicalFourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact F.comp (Uclm.comp C)

theorem physicalH1ComplexCarrierToL2Actual22_fourier
    (x : WeightedHilbert H1Weight22) (n : ℤ) :
    physicalFourier (physicalH1ComplexCarrierToL2Actual22 x) n = x n := by
  change physicalFourier (physicalFourierL2.symm
    ((weightedIsometry (fun _ : ℤ => (1 : ℝ))
      (weightedComparison H1Weight22 (fun _ : ℤ => (1 : ℝ)) 1
        (by norm_num) (fun k => by
          simpa only [one_mul] using h1Weight22_ge_one k) x)))) n = x n
  rw [physicalFourier_symm_apply]
  rw [weightedIsometry_apply]
  change weightedCoordinates (fun _ : ℤ => (1 : ℝ))
      (weightedComparison H1Weight22 (fun _ : ℤ => (1 : ℝ)) 1
        (by norm_num) (fun k => by
          simpa only [one_mul] using h1Weight22_ge_one k) x) n = x n
  simp only [weightedCoordinates, Real.sqrt_one, Complex.ofReal_one, one_mul]
  exact weightedComparison_apply H1Weight22 (fun _ : ℤ => (1 : ℝ)) 1
    (by norm_num) (fun k => by
      simpa only [one_mul] using h1Weight22_ge_one k) x n

theorem physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable
    (x : WeightedHilbert H1Weight22) :
    SobolevSquareSummable 1
      (physicalFourier (physicalH1ComplexCarrierToL2Actual22 x)) := by
  unfold SobolevSquareSummable
  have hs := (weightedHilbert_hasSum H1Weight22 x).summable
  change Summable (fun n : ℤ =>
    Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) *
      ‖physicalFourier (physicalH1ComplexCarrierToL2Actual22 x) n‖ ^ 2)
  apply hs.congr
  intro n
  rw [physicalH1ComplexCarrierToL2Actual22_fourier]
  simp only [sobolevModeWeight, NlsGge.Analysis.japaneseBracket_h1_weight]

end NlsGge.Schur
