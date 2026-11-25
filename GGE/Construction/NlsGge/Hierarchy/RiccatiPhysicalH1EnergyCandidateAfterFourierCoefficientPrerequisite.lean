import NlsGge.Analysis.H1Fourier
import NlsGge.Analysis.H1Multiplication
import NlsGge.Sobolev.SmoothFourier
import NlsGge.Hierarchy.RiccatiPhysicalFourierL2SymmCoefficientsSecond
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

/-! A generic H¹ Fourier-derivative class and bounded Q₂-energy candidate for
the actual period-one normalization. The derivative class is defined by its
Fourier multiplier and is not yet identified with the weak derivative of an
arbitrary H¹ representative. No Q₂ functional continuity claim is made. -/

namespace NlsGge.Pilot

open NlsGge.Analysis
open MeasureTheory

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The period-one Fourier multiplier coefficients for the candidate first
derivative class. -/
def physicalH1FourierDerivativeClassCoefficientsV2 (u : PhysicalL2) : ℤ → ℂ :=
  fun n => fourierMultiplier n * physicalFourier u n

private theorem physicalH1FourierDerivativeClassCoefficientsV2_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun n : ℤ => ‖physicalH1FourierDerivativeClassCoefficientsV2 u n‖ ^ 2) := by
  have hH1 : Summable (fun n : ℤ =>
      (1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2) := by
    simpa only [SobolevSquareSummable, japaneseBracket_h1_weight] using hu
  have hmajor := hH1.mul_left ((2 * Real.pi) ^ 2)
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _)
    (fun n => ?_) hmajor
  rw [physicalH1FourierDerivativeClassCoefficientsV2, norm_mul, norm_fourierMultiplier]
  have hn : |(n : ℝ)| ^ 2 ≤ 1 + (n : ℝ) ^ 2 := by
    rw [sq_abs]
    nlinarith
  have hπ : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  calc
    ((2 * Real.pi) * |(n : ℝ)| * ‖physicalFourier u n‖) ^ 2 =
        (2 * Real.pi) ^ 2 * (|(n : ℝ)| ^ 2 * ‖physicalFourier u n‖ ^ 2) := by ring
    _ ≤ (2 * Real.pi) ^ 2 *
        ((1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hn (sq_nonneg _)) hπ

/-- The genuine `PhysicalL2` class whose ordinary Fourier coefficients are
`2π i n` times those of the input. The definition uses the inverse of the
actual unitary physical Fourier map, not an unweighted sequence carrier. -/
def physicalH1FourierDerivativeClass (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) : PhysicalL2 :=
  physicalFourierL2.symm
    (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
      (physicalH1FourierDerivativeClassCoefficientsV2 u)
      (by simpa using physicalH1FourierDerivativeClassCoefficientsV2_summable u hu))

theorem physicalH1FourierDerivativeClass_fourier (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    physicalFourier (physicalH1FourierDerivativeClass u hu) n =
      fourierMultiplier n * physicalFourier u n := by
  simpa [physicalH1FourierDerivativeClass,
    physicalH1FourierDerivativeClassCoefficientsV2, weightedL2Element, weightedCoordinates] using
      (physicalFourier_symm_apply
        (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
          (physicalH1FourierDerivativeClassCoefficientsV2 u)
          (by simpa using physicalH1FourierDerivativeClassCoefficientsV2_summable u hu)) n)

theorem physicalH1FourierDerivativeClass_norm_le (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖physicalH1FourierDerivativeClass u hu‖ ≤
      (2 * Real.pi) * ‖physicalSobolevL2 1 u hu‖ := by
  have hD : ‖physicalH1FourierDerivativeClass u hu‖ ^ 2 =
      ∑' n : ℤ, ‖physicalH1FourierDerivativeClassCoefficientsV2 u n‖ ^ 2 := by
    rw [physicalH1FourierDerivativeClass, physicalFourierL2.symm.norm_map]
    simpa only [weightedL2Element_norm_sq, one_mul, physicalH1FourierDerivativeClassCoefficientsV2]
  have hU : ‖physicalSobolevL2 1 u hu‖ ^ 2 =
      ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2 := by
    rw [physicalSobolevL2_norm_sq]
    apply tsum_congr
    intro n
    rw [japaneseBracket_h1_weight]
  have hterm : ∀ n : ℤ,
      ‖physicalH1FourierDerivativeClassCoefficientsV2 u n‖ ^ 2 ≤
        (2 * Real.pi) ^ 2 * ((1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2) := by
    intro n
    rw [physicalH1FourierDerivativeClassCoefficientsV2, norm_mul, norm_fourierMultiplier]
    have hn : |(n : ℝ)| ^ 2 ≤ 1 + (n : ℝ) ^ 2 := by
      rw [sq_abs]
      nlinarith
    have hπ : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
    calc
      ((2 * Real.pi) * |(n : ℝ)| * ‖physicalFourier u n‖) ^ 2 =
          (2 * Real.pi) ^ 2 * (|(n : ℝ)| ^ 2 * ‖physicalFourier u n‖ ^ 2) := by ring
      _ ≤ (2 * Real.pi) ^ 2 *
          ((1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hn (sq_nonneg _)) hπ
  have hsum :
      (∑' n : ℤ, ‖physicalH1FourierDerivativeClassCoefficientsV2 u n‖ ^ 2) ≤
        (2 * Real.pi) ^ 2 *
          (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2) := by
    have hweighted : Summable (fun n : ℤ =>
        (1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2) := by
      simpa only [SobolevSquareSummable, japaneseBracket_h1_weight] using hu
    calc
      _ ≤ ∑' n : ℤ,
          (2 * Real.pi) ^ 2 * ((1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2) :=
        (physicalH1FourierDerivativeClassCoefficientsV2_summable u hu).tsum_le_tsum hterm
          (hweighted.mul_left ((2 * Real.pi) ^ 2))
      _ = (2 * Real.pi) ^ 2 *
          (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2) := by
        rw [tsum_mul_left]
  rw [← hD, ← hU] at hsum
  have hnonnegD : 0 ≤ ‖physicalH1FourierDerivativeClass u hu‖ := norm_nonneg _
  have hnonnegU : 0 ≤ (2 * Real.pi) * ‖physicalSobolevL2 1 u hu‖ := by positivity
  apply (sq_le_sq₀ hnonnegD hnonnegU).1
  nlinarith [hsum]

/-- A generic-H¹ Q₂-energy candidate. The quartic term uses the canonical
continuous Fourier representative, and the quadratic term uses the L² Fourier
multiplier class above. Its identification with the periodic Q₂ charge and
continuity as a functional remain separate results. -/
def physicalH1EnergyCandidate (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) : ℝ :=
  ‖physicalH1FourierDerivativeClass u hu‖ ^ 2 +
    ∫ x : PhysicalCircle, ‖physicalH1Continuous u hu x‖ ^ 4 ∂spatialMeasure

theorem physicalH1EnergyCandidate_quartic_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∫ x : PhysicalCircle, ‖physicalH1Continuous u hu x‖ ^ 4 ∂spatialMeasure ≤
      (‖physicalSobolevL2 1 u hu‖ * ‖reciprocalBracketL2‖) ^ 4 := by
  let f := physicalH1Continuous u hu
  have hf : Integrable (fun x : PhysicalCircle => ‖f x‖ ^ 4) spatialMeasure := by
    apply (f.continuous.norm.pow 4).integrable_of_hasCompactSupport
    exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  have hle : ∀ x : PhysicalCircle, ‖f x‖ ^ 4 ≤ ‖f‖ ^ 4 := by
    intro x
    exact pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm x) 4
  calc
    _ = ∫ x : PhysicalCircle, ‖f x‖ ^ 4 ∂spatialMeasure := by rfl
    _ ≤ ∫ _ : PhysicalCircle, ‖f‖ ^ 4 ∂spatialMeasure :=
      integral_mono_ae hf (integrable_const (‖f‖ ^ 4)) (Filter.Eventually.of_forall hle)
    _ = ‖f‖ ^ 4 := by simp
    _ ≤ (‖physicalSobolevL2 1 u hu‖ * ‖reciprocalBracketL2‖) ^ 4 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 4
      exact physicalH1Continuous_norm_bound u hu

theorem physicalH1EnergyCandidate_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    physicalH1EnergyCandidate u hu ≤
      ((2 * Real.pi) * ‖physicalSobolevL2 1 u hu‖) ^ 2 +
        (‖physicalSobolevL2 1 u hu‖ * ‖reciprocalBracketL2‖) ^ 4 := by
  unfold physicalH1EnergyCandidate
  apply add_le_add
  · exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
      (physicalH1FourierDerivativeClass_norm_le u hu)
  · exact physicalH1EnergyCandidate_quartic_bound u hu

end NlsGge.Pilot
