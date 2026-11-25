import NlsGge.GK38.AngleSegmentGeometry

/-! Source-only scalar numerator estimate for book I.15 Lemma15.1.
The explicit root-distance premise is to be earned from the actual P7 roots. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

theorem angleSegment_numerator38 (a b μ σ : ℂ) (t L : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hL : 0 ≤ L)
    (hnear : ‖μ - a‖ ≤ ‖μ - b‖) (hσ : ‖σ - b‖ ≤ L * ‖a - b‖) :
    ‖σ - (a + (t : ℂ) * (μ - a))‖ ≤
      (1 + 2 * L) * ‖b - (a + (t : ℂ) * (μ - a))‖ := by
  let z : ℂ := a + (t : ℂ) * (μ - a)
  have hsep : ‖a - b‖ ≤ 2 * ‖b - z‖ := by
    have h := angleSegment_far_root38 a b μ t ht0 ht1 hnear
    rw [norm_sub_rev (a + (t : ℂ) * (μ - a)) b] at h
    dsimp [z]
    linarith
  have htri : ‖σ - z‖ ≤ ‖σ - b‖ + ‖b - z‖ := by
    calc
      ‖σ - z‖ = ‖(σ - b) + (b - z)‖ := by congr 1; ring
      _ ≤ ‖σ - b‖ + ‖b - z‖ := norm_add_le _ _
  have hscaled := mul_le_mul_of_nonneg_left hsep hL
  change ‖σ - z‖ ≤ (1 + 2 * L) * ‖b - z‖
  nlinarith

theorem angleSegment_numerator_quotient38 (a b μ σ : ℂ) (t L : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hL : 0 ≤ L) (hab : a ≠ b)
    (hnear : ‖μ - a‖ ≤ ‖μ - b‖) (hσ : ‖σ - b‖ ≤ L * ‖a - b‖) :
    ‖(σ - (a + (t : ℂ) * (μ - a))) /
      (b - (a + (t : ℂ) * (μ - a)))‖ ≤ 1 + 2 * L := by
  have hgap : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hsep := angleSegment_far_root38 a b μ t ht0 ht1 hnear
  rw [norm_sub_rev (a + (t : ℂ) * (μ - a)) b] at hsep
  have hden : 0 < ‖b - (a + (t : ℂ) * (μ - a))‖ := by linarith
  rw [norm_div, div_le_iff₀ hden]
  exact angleSegment_numerator38 a b μ σ t L ht0 ht1 hL hnear hσ

end
end NlsGge.GK38
