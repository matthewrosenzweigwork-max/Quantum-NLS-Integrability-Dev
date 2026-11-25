import Mathlib
import NlsGge.Atomic.KST.KST004
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST019
import NlsGge.Atomic.KST.KST020
import NlsGge.ThirdConsultation.KST.KST047Host
import NlsGge.Atomic.KST.KST047

/- KST-048 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST048.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from design STATEMENTS/KST.md "## KST-048"
   (gpt6pro_followup10; no Pro round entry touches KST-048).
   Route = source skeleton (WORK_PACKETS KST-048.md): Cauchy estimate with radius 7*pi/16 on the closed source
   strip (|z - center| <= pi/16 on the 2r disc since r <= pi/48), then the mean value inequality on the convex disc
   gives |b z - b sigma| <= 2r/21, combined with KST-047.  Support: KST047Host (Balanced, rootRadius), kst047. -/
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST004

namespace NlsGge.ThirdConsultation.KST

/-- Cauchy estimate on the source strip: coefficient bound `π/48` on the closed strip gives
`|f'| ≤ 1/21` at every point within `π/16` of the center. -/
theorem kst048_cauchy_strip (n : ℤ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectralStrip n))
    (hb : ∀ w ∈ spectralStrip n, ‖f w‖ ≤ Real.pi / 48)
    (z : ℂ) (hz : ‖z - center n‖ ≤ Real.pi / 16) :
    DifferentiableAt ℂ f z ∧ ‖deriv f z‖ ≤ (1 / 21 : ℝ) := by
  have hρ : 0 < 7 * Real.pi / 16 := by positivity
  have hsub : Metric.closedBall z (7 * Real.pi / 16) ⊆ spectralStrip n := by
    refine Set.Subset.trans ?_ (closedBall_subset_strip_of_le n (r := Real.pi / 2) (le_refl _))
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw ⊢
    calc ‖w - center n‖ = ‖(w - z) + (z - center n)‖ := by congr 1; ring
      _ ≤ ‖w - z‖ + ‖z - center n‖ := norm_add_le _ _
      _ ≤ Real.pi / 2 := by linarith
  have hzs : z ∈ spectralStrip n :=
    hsub (Metric.mem_closedBall_self hρ.le)
  have hdiffOn : DifferentiableOn ℂ f (spectralStrip n) := fun w hw => (hf w hw).differentiableAt.differentiableWithinAt
  refine ⟨(hf z hzs).differentiableAt, ?_⟩
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (f := f)
    (R := 7 * Real.pi / 16) (C := Real.pi / 48) hρ
    (hdiffOn.diffContOnCl_ball hsub)
    (fun w hw => hb w (hsub (Metric.sphere_subset_closedBall hw)))
  have heq : Real.pi / 48 / (7 * Real.pi / 16) = (1 / 21 : ℝ) := by
    field_simp
    ring
  rwa [heq] at hcauchy

theorem kst048 (n : ℤ) (a b c : ℂ → ℂ) (σ : ℂ)
    (h : Balanced n a b c σ) :
  ∀ z ∈ Metric.closedBall σ (2*rootRadius b c σ),
    HasDerivAt a (deriv a z) z ∧ HasDerivAt b (deriv b z) z ∧
    HasDerivAt c (deriv c z) z ∧
    ‖deriv a z‖ ≤ (1/21 : ℝ) ∧ ‖deriv b z‖ ≤ (1/21 : ℝ) ∧
    ‖deriv c z‖ ≤ (1/21 : ℝ) ∧
    (5/21 : ℝ)*rootRadius b c σ ≤ ‖b z‖ ∧
    ‖b z‖ ≤ (65/21 : ℝ)*rootRadius b c σ ∧
    (5/21 : ℝ)*rootRadius b c σ ≤ ‖c z‖ ∧
    ‖c z‖ ≤ (65/21 : ℝ)*rootRadius b c σ ∧
    b z ≠ 0 ∧ c z ≠ 0 ∧ ‖b z/c z‖ ≤ 13 ∧ ‖c z/b z‖ ≤ 13 := by
  obtain ⟨-, hbl, hbu, hcl, hcu, -⟩ := kst047 n a b c σ h
  obtain ⟨⟨ha, hb, hc, hbd⟩, -, hσc, hbc, -, -⟩ := h
  have hb0 : b σ ≠ 0 := left_ne_zero_of_mul hbc
  have hc0 : c σ ≠ 0 := right_ne_zero_of_mul hbc
  have hB : 0 < ‖b σ‖ := norm_pos_iff.2 hb0
  have hC : 0 < ‖c σ‖ := norm_pos_iff.2 hc0
  set r := rootRadius b c σ with hr
  have hstrip : σ ∈ spectralStrip n := by
    apply closedBall_subset_strip_of_le n (r := Real.pi / 48) (by linarith [Real.pi_pos])
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hσc
  obtain ⟨-, hbπ, hcπ⟩ := hbd σ hstrip
  have hrdef : r = Real.sqrt (‖b σ‖ * ‖c σ‖) := by
    rw [hr, rootRadius, norm_mul]
  have hrπ : r ≤ Real.pi / 48 := by
    rw [hrdef]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have := mul_le_mul hbπ hcπ hC.le (by positivity)
    nlinarith [this]
  have hr0 : 0 < r := by linarith
  intro z hz
  have hzr : ‖z - σ‖ ≤ 2 * r := by
    simpa [dist_eq_norm] using Metric.mem_closedBall.1 hz
  have hzc : ‖z - center n‖ ≤ Real.pi / 16 := by
    calc ‖z - center n‖ = ‖(z - σ) + (σ - center n)‖ := by congr 1; ring
      _ ≤ ‖z - σ‖ + ‖σ - center n‖ := norm_add_le _ _
      _ ≤ Real.pi / 16 := by linarith
  -- derivative bounds, uniformly on the disc
  have hdisc : ∀ w ∈ Metric.closedBall σ (2 * r), ‖w - center n‖ ≤ Real.pi / 16 := by
    intro w hw
    have hwr : ‖w - σ‖ ≤ 2 * r := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.1 hw
    calc ‖w - center n‖ = ‖(w - σ) + (σ - center n)‖ := by congr 1; ring
      _ ≤ ‖w - σ‖ + ‖σ - center n‖ := norm_add_le _ _
      _ ≤ Real.pi / 16 := by linarith
  have hA : ∀ w ∈ Metric.closedBall σ (2 * r),
      DifferentiableAt ℂ a w ∧ ‖deriv a w‖ ≤ (1 / 21 : ℝ) := fun w hw =>
    kst048_cauchy_strip n a ha (fun v hv => (hbd v hv).1) w (hdisc w hw)
  have hBd : ∀ w ∈ Metric.closedBall σ (2 * r),
      DifferentiableAt ℂ b w ∧ ‖deriv b w‖ ≤ (1 / 21 : ℝ) := fun w hw =>
    kst048_cauchy_strip n b hb (fun v hv => (hbd v hv).2.1) w (hdisc w hw)
  have hCd : ∀ w ∈ Metric.closedBall σ (2 * r),
      DifferentiableAt ℂ c w ∧ ‖deriv c w‖ ≤ (1 / 21 : ℝ) := fun w hw =>
    kst048_cauchy_strip n c hc (fun v hv => (hbd v hv).2.2) w (hdisc w hw)
  have hσmem : σ ∈ Metric.closedBall σ (2 * r) := Metric.mem_closedBall_self (by linarith)
  have hconv : Convex ℝ (Metric.closedBall σ (2 * r)) := convex_closedBall σ (2 * r)
  have hbdiff : ‖b z - b σ‖ ≤ (1 / 21 : ℝ) * ‖z - σ‖ :=
    hconv.norm_image_sub_le_of_norm_deriv_le (fun w hw => (hBd w hw).1)
      (fun w hw => (hBd w hw).2) hσmem hz
  have hcdiff : ‖c z - c σ‖ ≤ (1 / 21 : ℝ) * ‖z - σ‖ :=
    hconv.norm_image_sub_le_of_norm_deriv_le (fun w hw => (hCd w hw).1)
      (fun w hw => (hCd w hw).2) hσmem hz
  have hbz1 : ‖b σ‖ - ‖b z‖ ≤ ‖b z - b σ‖ := by
    have := norm_sub_norm_le (b σ) (b z)
    rwa [norm_sub_rev] at this
  have hbz2 : ‖b z‖ - ‖b σ‖ ≤ ‖b z - b σ‖ := norm_sub_norm_le _ _
  have hcz1 : ‖c σ‖ - ‖c z‖ ≤ ‖c z - c σ‖ := by
    have := norm_sub_norm_le (c σ) (c z)
    rwa [norm_sub_rev] at this
  have hcz2 : ‖c z‖ - ‖c σ‖ ≤ ‖c z - c σ‖ := norm_sub_norm_le _ _
  have hbzl : (5 / 21 : ℝ) * r ≤ ‖b z‖ := by nlinarith
  have hbzu : ‖b z‖ ≤ (65 / 21 : ℝ) * r := by nlinarith
  have hczl : (5 / 21 : ℝ) * r ≤ ‖c z‖ := by nlinarith
  have hczu : ‖c z‖ ≤ (65 / 21 : ℝ) * r := by nlinarith
  have hbzpos : 0 < ‖b z‖ := lt_of_lt_of_le (by positivity) hbzl
  have hczpos : 0 < ‖c z‖ := lt_of_lt_of_le (by positivity) hczl
  refine ⟨(hA z hz).1.hasDerivAt, (hBd z hz).1.hasDerivAt, (hCd z hz).1.hasDerivAt,
    (hA z hz).2, (hBd z hz).2, (hCd z hz).2, hbzl, hbzu, hczl, hczu,
    norm_pos_iff.1 hbzpos, norm_pos_iff.1 hczpos, ?_, ?_⟩
  · rw [norm_div, div_le_iff₀ hczpos]
    nlinarith
  · rw [norm_div, div_le_iff₀ hbzpos]
    nlinarith

end NlsGge.ThirdConsultation.KST
end
