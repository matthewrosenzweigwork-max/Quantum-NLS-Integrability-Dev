import NlsGge.Analysis.EllipseDeformation
import NlsGge.GK38.ContourActionDeformation

set_option autoImplicit false
open Set Metric MeasureTheory
open NlsGge.GK38 NlsGge.Pilot
namespace NlsGge.GK38.ActionEllipseDomain
noncomputable section

theorem gap_cut_im_zero (u : PhysicalL2) {z : ℂ} (hz : z ∈ gapSegments38 (realSlice u)) :
    z.im = 0 := by
  obtain ⟨n, hn⟩ := mem_iUnion.mp hz
  obtain ⟨a, b, _, _, _, he⟩ := hn
  have hi := congrArg Complex.im he
  rw [(lamPlus_real u n).1, (lamPlus_real u n).2] at hi
  simpa only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
    Complex.ofReal_re, mul_zero, zero_mul, add_zero] using hi.symm

theorem curve_im (c : ℂ) (r δ θ : ℝ) (hc : c.im = 0) :
    (NlsGge.Analysis.EllipseDeformation.curve c r δ θ).im = δ * r * Real.sin θ := by
  simp [NlsGge.Analysis.EllipseDeformation.curve, Complex.add_im, Complex.mul_im, Complex.sin_ofReal_re, hc]

theorem ellipse_avoids_cut (u : PhysicalL2) (c : ℂ) (r δ : ℝ)
    (hc : c.im = 0) (hr : 0 < r) (hδ : 0 < δ)
    (hs : sphere c r ⊆ actionCutDomain38 (realSlice u)) (θ : ℝ) :
    NlsGge.Analysis.EllipseDeformation.curve c r δ θ ∈ actionCutDomain38 (realSlice u) := by
  intro hcut
  have hi := gap_cut_im_zero u hcut
  rw [curve_im c r δ θ hc] at hi
  have hz : Real.sin θ = 0 := (mul_eq_zero.mp hi).resolve_left (ne_of_gt (mul_pos hδ hr))
  have he : NlsGge.Analysis.EllipseDeformation.curve c r δ θ = circleMap c r θ := by
    rw [← NlsGge.Analysis.EllipseDeformation.curve_one c r θ]
    simp [NlsGge.Analysis.EllipseDeformation.curve, hz]
  rw [he] at hcut
  exact hs (circleMap_mem_sphere c hr.le θ) hcut

theorem interpolated_height_pos {δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < δ + (1 - δ) * t := by
  by_cases hz : t = 0
  · simpa [hz] using hδ
  · have hp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
    have hn : 0 ≤ (1 - t) * δ := mul_nonneg (sub_nonneg.mpr ht.2) hδ.le
    nlinarith

theorem actual_action_ellipse_eq_circle (u : PhysicalL2) (c : ℂ) (r δ : ℝ)
    (hc : c.im = 0) (hr : 0 < r) (hδ : 0 < δ)
    (hs : sphere c r ⊆ actionCutDomain38 (realSlice u)) :
    IntervalIntegrable (fun θ => NlsGge.Analysis.EllipseDeformation.velocity r δ θ *
      actionIntegrand38 (realSlice u) (NlsGge.Analysis.EllipseDeformation.curve c r δ θ))
        volume 0 (2 * Real.pi) ∧
      CircleIntegrable (actionIntegrand38 (realSlice u)) c r ∧
      (∫ θ in (0 : ℝ)..2 * Real.pi, NlsGge.Analysis.EllipseDeformation.velocity r δ θ *
        actionIntegrand38 (realSlice u) (NlsGge.Analysis.EllipseDeformation.curve c r δ θ)) =
        circleIntegral (actionIntegrand38 (realSlice u)) c r := by
  apply NlsGge.Analysis.EllipseDeformation.ellipse_integral_eq_circle c r δ
    (isOpen_actionCutDomain38 (realSlice u) (realSlice_mem_gkW u))
    (actionIntegrand_analytic38 (realSlice u) (realSlice_mem_gkW u))
  intro t ht θ _
  exact ellipse_avoids_cut u c r _ hc hr (interpolated_height_pos hδ ht) hs θ

end
end NlsGge.GK38.ActionEllipseDomain
