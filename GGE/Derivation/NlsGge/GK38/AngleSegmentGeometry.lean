import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Source-only preparation for book I.15 Lemma15.1.
No actual psi-family, admissible-path or angle theorem is claimed here. -/
set_option autoImplicit false
open Set MeasureTheory
namespace NlsGge.GK38
noncomputable section

/-- The difference of squared distances is affine along a real segment. -/
theorem angleSegment_sq_difference38 (a b μ : ℂ) (t : ℝ) :
    ‖a + (t : ℂ) * (μ - a) - b‖ ^ 2 -
        ‖a + (t : ℂ) * (μ - a) - a‖ ^ 2 =
      (1 - t) * ‖a - b‖ ^ 2 + t * (‖μ - b‖ ^ 2 - ‖μ - a‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Choosing the nearer endpoint places the entire joining segment on its side
of the perpendicular bisector, including both segment endpoints. -/
theorem angleSegment_nearest38 (a b μ : ℂ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hnear : ‖μ - a‖ ≤ ‖μ - b‖) :
    ‖a + (t : ℂ) * (μ - a) - a‖ ≤
      ‖a + (t : ℂ) * (μ - a) - b‖ := by
  have hs : 0 ≤ ‖μ - b‖ ^ 2 - ‖μ - a‖ ^ 2 := by
    nlinarith [norm_nonneg (μ - a), norm_nonneg (μ - b)]
  have hid := angleSegment_sq_difference38 a b μ t
  have hnonneg : 0 ≤
      ‖a + (t : ℂ) * (μ - a) - b‖ ^ 2 -
        ‖a + (t : ℂ) * (μ - a) - a‖ ^ 2 := by
    rw [hid]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (sq_nonneg _))
      (mul_nonneg ht0 hs)
  nlinarith [norm_nonneg (a + (t : ℂ) * (μ - a) - a),
    norm_nonneg (a + (t : ℂ) * (μ - a) - b)]

/-- The opposite root stays at least half the gap away from that segment. -/
theorem angleSegment_far_root38 (a b μ : ℂ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hnear : ‖μ - a‖ ≤ ‖μ - b‖) :
    ‖a - b‖ / 2 ≤ ‖a + (t : ℂ) * (μ - a) - b‖ := by
  have hnearseg := angleSegment_nearest38 a b μ t ht0 ht1 hnear
  have htri := dist_triangle a (a + (t : ℂ) * (μ - a)) b
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev a (a + (t : ℂ) * (μ - a))] at htri
  linarith

/-- The actual singular majorant is integrable before its integral is used. -/
theorem angleSegment_majorant_integrable38 :
    IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) volume 0 1 :=
  intervalIntegral.intervalIntegrable_rpow' (by norm_num)

theorem angleSegment_majorant_integral38 :
    (∫ t : ℝ in (0 : ℝ)..1, t ^ (-(1 : ℝ) / 2)) = 2 := by
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num

end
end NlsGge.GK38
