import NlsGge.Schur.PhysicalH1ComplexCarrierSchurBridge
import NlsGge.Hierarchy.RiccatiPhysicalH1CarrierAfterUnweightedCoordinateSecond
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev38.SobolevCarrier38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.Sobolev38

/-! # Q0: the `H^k` field as an `L²` element, and its `H¹` carrier

`sobolevToL2_38 k` sends an `H^k` Fourier carrier to the `L²` function with the same Fourier coefficients.
`sobolevToH1_38 k` (for `k ≥ 1`) sends it to the complex `H¹` carrier used by E03 / E03-cont. -/

local instance sobolevToL2Fact38 : Fact (∀ _ : ℤ, 0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem one_le_sobolevModeWeight38 (k : ℕ) (n : ℤ) : (1 : ℝ) ≤ sobolevModeWeight (k : ℝ) n := by
  unfold sobolevModeWeight
  exact Real.one_le_rpow (japaneseBracket_one_le n) (by positivity)

theorem sobolevModeWeight_one_le38 (k : ℕ) (hk : 1 ≤ k) (n : ℤ) :
    sobolevModeWeight (1 : ℝ) n ≤ 1 * sobolevModeWeight (k : ℝ) n := by
  unfold sobolevModeWeight
  rw [one_mul]
  exact Real.rpow_le_rpow_of_exponent_le (japaneseBracket_one_le n)
    (by have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith)

/-- The `H^k` carrier mapped to `L²` (coordinates are the identity). -/
def sobolevToL2_38 (k : ℕ) : SobolevHilbert (k : ℝ) →L[ℝ] PhysicalL2 :=
  ((physicalFourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
    (physicalH1UnweightedToLp.comp
      (weightedRealComparisonContinuous (sobolevModeWeight (k : ℝ)) (fun _ : ℤ => (1 : ℝ)) 1
        (by norm_num) (fun n => by simpa only [one_mul] using one_le_sobolevModeWeight38 k n)))

theorem sobolevToL2_38_fourier (k : ℕ) (y : SobolevHilbert (k : ℝ)) (n : ℤ) :
    physicalFourier (sobolevToL2_38 k y) n = (show WeightedHilbert (sobolevModeWeight (k:ℝ)) from y) n := by
  change physicalFourier (physicalFourierL2.symm (physicalH1UnweightedToLp
    (weightedRealComparisonContinuous (sobolevModeWeight (k : ℝ)) (fun _ : ℤ => (1 : ℝ)) 1
      (by norm_num) (fun n => by simpa only [one_mul] using one_le_sobolevModeWeight38 k n) y))) n = _
  rw [physicalFourier_symm_apply]
  change (weightedIsometry (fun _ : ℤ => (1 : ℝ))
    (show WeightedHilbert (fun _ : ℤ => (1 : ℝ)) from
      weightedRealComparisonContinuous (sobolevModeWeight (k : ℝ)) (fun _ : ℤ => (1 : ℝ)) 1
        (by norm_num) (fun n => by simpa only [one_mul] using one_le_sobolevModeWeight38 k n) y)) n = _
  rw [weightedIsometry_apply]
  simp only [weightedCoordinates, Real.sqrt_one, Complex.ofReal_one, one_mul]
  rfl

theorem sobolevToL2_38_sobolev (k : ℕ) (y : SobolevHilbert (k : ℝ)) :
    SobolevSquareSummable (k : ℝ) (physicalFourier (sobolevToL2_38 k y)) := by
  unfold SobolevSquareSummable
  have hs := (weightedHilbert_hasSum (sobolevModeWeight (k : ℝ))
    (show WeightedHilbert (sobolevModeWeight (k : ℝ)) from y)).summable
  apply hs.congr
  intro n
  rw [sobolevToL2_38_fourier]
  rfl

/-- continuous map into the complex H¹ carrier used by E03 / E03-cont -/
def sobolevToH1_38 (k : ℕ) (hk : 1 ≤ k) :
    SobolevHilbert (k : ℝ) → WeightedHilbert (sobolevModeWeight (1:ℝ)) :=
  fun y => weightedRealComparisonContinuous (sobolevModeWeight (k : ℝ)) (sobolevModeWeight (1 : ℝ)) 1
    (by norm_num) (fun n => sobolevModeWeight_one_le38 k hk n) y

theorem sobolevToH1_38_apply (k : ℕ) (hk : 1 ≤ k) (y : SobolevHilbert (k : ℝ)) (n : ℤ) :
    (sobolevToH1_38 k hk y) n = (show WeightedHilbert (sobolevModeWeight (k:ℝ)) from y) n := rfl

theorem continuous_sobolevToH1_38 (k : ℕ) (hk : 1 ≤ k) : Continuous (sobolevToH1_38 k hk) :=
  (weightedRealComparisonContinuous (sobolevModeWeight (k : ℝ)) (sobolevModeWeight (1 : ℝ)) 1
    (by norm_num) (fun n => sobolevModeWeight_one_le38 k hk n)).continuous

theorem carrier_sobolevToH1_38 (k : ℕ) (hk : 1 ≤ k) (y : SobolevHilbert (k : ℝ)) :
    physicalH1ComplexCarrierToL2Actual22 (sobolevToH1_38 k hk y) = sobolevToL2_38 k y := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply, physicalH1ComplexCarrierToL2Actual22_fourier,
    sobolevToL2_38_fourier]
  rfl

theorem norm_sobolevToH1_38_le (k : ℕ) (hk : 1 ≤ k) (y : SobolevHilbert (k : ℝ)) :
    ‖sobolevToH1_38 k hk y‖ ≤ ‖y‖ := by
  change ‖weightedRealComparisonLinear (sobolevModeWeight (k : ℝ)) (sobolevModeWeight (1 : ℝ)) 1
    (by norm_num) (fun n => sobolevModeWeight_one_le38 k hk n) y‖ ≤ ‖y‖
  have h := weightedRealComparison_norm_le (sobolevModeWeight (k : ℝ)) (sobolevModeWeight (1 : ℝ)) 1
    (by norm_num) (fun n => sobolevModeWeight_one_le38 k hk n) y
  simpa only [Real.sqrt_one, one_mul] using h

end NlsGge.SpectralFoundations
