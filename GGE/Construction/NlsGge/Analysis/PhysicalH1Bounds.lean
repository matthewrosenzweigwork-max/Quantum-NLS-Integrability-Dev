import NlsGge.Analysis.ConvolutionBounds
import NlsGge.Sobolev.PeriodicBridge

namespace NlsGge.Analysis

open NlsGge.Pilot

theorem japaneseBracket_h1_weight (p : ℤ) :
    Real.rpow (japaneseBracket p) (2 * (1 : ℝ)) = 1 + (p : ℝ) ^ 2 := by
  rw [mul_one, Real.rpow_eq_pow, Real.rpow_two]
  unfold japaneseBracket
  exact Real.sq_sqrt (by positivity)

/-- The numerical block sum specialized to a genuine physical L2 field in its Fourier H1 domain. -/
theorem physicalH1_convolution_tsum_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    (∑' p : ℤ, ‖physicalFourier u p‖ ^ 2 * inverseSquareConvolution (p - n)) ≤
      (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
        ‖physicalSobolevL2 1 u hu‖ ^ 2 := by
  have hs : Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * ‖physicalFourier u p‖ ^ 2) := by
    simpa only [SobolevSquareSummable, japaneseBracket_h1_weight] using hu
  have hnorm := physicalSobolevL2_norm_sq 1 u hu
  simp only [japaneseBracket_h1_weight] at hnorm
  rw [hnorm]
  exact weighted_convolution_tsum_bound (fun p => ‖physicalFourier u p‖ ^ 2)
    (fun p => sq_nonneg _) hs n

/-- The source nonresonant column sum with the actual source Fourier H1 norm. -/
theorem physicalH1_column_nonresonant_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) (hn : n ≠ 0) :
    (∑' p : {p : ℤ // p ≠ n}, ‖physicalFourier u p.val‖ ^ 2 * inverseSquare (n - p.val)) ≤
      (2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u hu‖ ^ 2 := by
  have hs : Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * ‖physicalFourier u p‖ ^ 2) := by
    simpa only [SobolevSquareSummable, japaneseBracket_h1_weight] using hu
  have hnorm := physicalSobolevL2_norm_sq 1 u hu
  simp only [japaneseBracket_h1_weight] at hnorm
  rw [hnorm]
  exact weighted_column_nonresonant_bound (fun p => ‖physicalFourier u p‖ ^ 2)
    (fun p => sq_nonneg _) hs n hn

end NlsGge.Analysis
