import NlsGge.Analysis.PhysicalH1Bounds
import NlsGge.Analysis.ReciprocalBracket

set_option autoImplicit false
noncomputable section
namespace NlsGge.Analysis
open NlsGge.Pilot

/-- A genuine fixed l2 sequence, not a norm assigned to a nonsummable reciprocal sequence. -/
def reciprocalBracketL2 : lp (fun _ : ℤ => ℂ) 2 :=
  weightedL2Element (fun p => 1 / (1 + (p : ℝ) ^ 2))
    (fun p => by positivity) (fun _ => (1 : ℂ))
    (by simpa using summable_reciprocal_bracket_square)

theorem reciprocalBracketL2_norm_sq :
    ‖reciprocalBracketL2‖ ^ 2 = ∑' p : ℤ, 1 / (1 + (p : ℝ) ^ 2) := by
  unfold reciprocalBracketL2
  rw [weightedL2Element_norm_sq]
  simp

theorem reciprocalBracketL2_norm_sq_bound :
    ‖reciprocalBracketL2‖ ^ 2 ≤ 1 + inverseSquareTotal := by
  rw [reciprocalBracketL2_norm_sq]
  exact reciprocal_bracket_square_tsum_bound

theorem physicalH1_reciprocal_norm_product (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (p : ℤ) :
    ‖physicalSobolevL2 1 u hu p‖ * ‖reciprocalBracketL2 p‖ = ‖physicalFourier u p‖ := by
  have hf : ‖physicalSobolevL2 1 u hu p‖ ^ 2 =
      (1 + (p : ℝ) ^ 2) * ‖physicalFourier u p‖ ^ 2 := by
    change ‖weightedCoordinates (fun q => Real.rpow (japaneseBracket q) (2 * (1 : ℝ)))
      (physicalFourier u) p‖ ^ 2 = _
    have hw : ∀ q : ℤ, 0 ≤ Real.rpow (japaneseBracket q) (2 * (1 : ℝ)) := by
      intro q
      rw [japaneseBracket_h1_weight]
      positivity
    have h := weightedCoordinates_norm_sq
      (fun q => Real.rpow (japaneseBracket q) (2 * (1 : ℝ))) hw (physicalFourier u) p
    simpa only [japaneseBracket_h1_weight] using h
  have hg : ‖reciprocalBracketL2 p‖ ^ 2 = 1 / (1 + (p : ℝ) ^ 2) := by
    change ‖weightedCoordinates (fun q => 1 / (1 + (q : ℝ) ^ 2))
      (fun _ => (1 : ℂ)) p‖ ^ 2 = _
    rw [weightedCoordinates_norm_sq _ (fun q => by positivity)]
    simp
  apply (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)).1
  rw [mul_pow, hf, hg]
  have hden : 1 + (p : ℝ) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hden] <;> ring

/-- Actual absolute Fourier summability is derived from the physical H1 domain. -/
theorem physicalH1_absolute_fourier_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun p : ℤ => ‖physicalFourier u p‖) := by
  have hs := lp.summable_mul
    (by rw [Real.holderConjugate_iff]; norm_num)
    (physicalSobolevL2 1 u hu) reciprocalBracketL2
  simpa only [physicalH1_reciprocal_norm_product] using hs

theorem physicalH1_absolute_fourier_tsum_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    (∑' p : ℤ, ‖physicalFourier u p‖) ≤
      ‖physicalSobolevL2 1 u hu‖ * ‖reciprocalBracketL2‖ := by
  have hs := physicalH1_absolute_fourier_summable u hu
  have h := lp.tsum_mul_le_mul_norm'
    (by rw [Real.holderConjugate_iff]; norm_num)
    (physicalSobolevL2 1 u hu) reciprocalBracketL2
  simpa only [physicalH1_reciprocal_norm_product] using h

end NlsGge.Analysis


set_option autoImplicit false
noncomputable section
namespace NlsGge.Analysis
open MeasureTheory
open NlsGge.Pilot

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

theorem physicalH1_continuous_fourier_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun p : ℤ => physicalFourier u p • fourier (T := (1 : ℝ)) p) := by
  apply Summable.of_norm
  simpa only [norm_smul, fourier_norm, mul_one] using physicalH1_absolute_fourier_summable u hu

/-- Its true convergent continuous Fourier series will be proved to represent the original L2 field. -/
def physicalH1Continuous (u : PhysicalL2)
    (_hu : SobolevSquareSummable 1 (physicalFourier u)) : C(PhysicalCircle, ℂ) :=
  ∑' p : ℤ, physicalFourier u p • fourier (T := (1 : ℝ)) p

theorem physicalH1Continuous_hasSum (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    HasSum (fun p : ℤ => physicalFourier u p • fourier (T := (1 : ℝ)) p)
      (physicalH1Continuous u hu) :=
  (physicalH1_continuous_fourier_summable u hu).hasSum

/-- The representative is identified with the actual field by genuine L2 Fourier reconstruction. -/
theorem physicalH1Continuous_toLp (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ContinuousMap.toLp 2 spatialMeasure ℂ (physicalH1Continuous u hu) = u := by
  have h := (ContinuousMap.toLp 2 spatialMeasure ℂ).hasSum (physicalH1Continuous_hasSum u hu)
  have hl := hasSum_fourier_series_L2 (T := (1 : ℝ)) u
  simp only [map_smul] at h
  change HasSum (fun p : ℤ => physicalFourier u p • fourierLp (T := (1 : ℝ)) 2 p)
    (ContinuousMap.toLp 2 spatialMeasure ℂ (physicalH1Continuous u hu)) at h
  exact h.unique hl

theorem physicalH1Continuous_norm_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖physicalH1Continuous u hu‖ ≤ ‖physicalSobolevL2 1 u hu‖ * ‖reciprocalBracketL2‖ := by
  have hs := physicalH1_continuous_fourier_summable u hu
  calc
    _ ≤ ∑' p : ℤ, ‖physicalFourier u p • fourier (T := (1 : ℝ)) p‖ :=
      norm_tsum_le_tsum_norm (by
        simpa only [norm_smul, fourier_norm, mul_one] using physicalH1_absolute_fourier_summable u hu)
    _ = ∑' p : ℤ, ‖physicalFourier u p‖ := by simp only [norm_smul, fourier_norm, mul_one]
    _ ≤ _ := physicalH1_absolute_fourier_tsum_bound u hu

end NlsGge.Analysis
