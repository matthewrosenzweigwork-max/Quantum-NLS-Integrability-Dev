import NlsGge.GK38.MolnarPreparation
import NlsGge.Analysis.PhysicalH1Bounds

set_option autoImplicit false

namespace NlsGge.GK38.MolnarBounds38

open NlsGge.Pilot NlsGge.Schur NlsGge.SpectralFoundations NlsGge.GK38

/-- The literal source pair-weight estimate uses integer frequencies, including zero. -/
theorem sourcePairWeight_le_derivative38 (n : ℤ) :
    2 * (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 ≤
      3 * (1 + (2 * Real.pi * (n : ℝ)) ^ 2) := by
  by_cases hn0 : n = 0
  · subst n
    norm_num
  · have ha : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
    have hr : 6 ≤ |2 * Real.pi * (n : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * Real.pi)]
      calc
        (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
        _ = (2 * Real.pi) * 1 := by ring
        _ ≤ (2 * Real.pi) * |(n : ℝ)| := mul_le_mul_of_nonneg_left ha (by positivity)
    have hprod := mul_nonneg (abs_nonneg (2 * Real.pi * (n : ℝ)))
      (show 0 ≤ |2 * Real.pi * (n : ℝ)| - 4 by linarith)
    nlinarith [sq_abs (2 * Real.pi * (n : ℝ))]

/-- The actual H1 Fourier condition gives genuine summability for the source's pi weights. -/
theorem sourcePairFourier_summable38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun n : ℤ =>
      (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 * ‖physicalFourier u n‖ ^ 2) := by
  have hs : Summable (fun n : ℤ => japaneseBracket n ^ 2 * ‖physicalFourier u n‖ ^ 2) := by
    simpa only [SobolevSquareSummable, NlsGge.Analysis.japaneseBracket_h1_weight, japaneseBracket_sq] using hu
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hs.mul_left ((1 + 2 * Real.pi) ^ 2))
  have h := mul_le_mul_of_nonneg_right (molnarWeight_le_japanese38 1 n)
    (sq_nonneg ‖physicalFourier u n‖)
  simpa only [mul_assoc] using h

/-- Every actual H1 potential is realized by the existing physical Sobolev embedding. -/
theorem exists_actual_H1_carrier38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∃ y : SobolevHilbert ((1 : ℕ) : ℝ), sobolevToL2_38 1 y = u := by
  obtain ⟨y, hy⟩ := exists_sobolev_link38 ((1 : ℕ) : ℝ) u (by simpa only [Nat.cast_one] using hu)
  refine ⟨y, ?_⟩
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply, sobolevToL2_38_fourier]
  exact hy n

end NlsGge.GK38.MolnarBounds38
