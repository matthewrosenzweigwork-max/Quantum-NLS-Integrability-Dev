                                                                                                                                                                                                                                                          
                                                                                   
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST019
import NlsGge.GK38.Lib.Rouche
import Mathlib

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NlsGge.ThirdConsultation.KST

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003
open NlsGge.Atomic.KST004 NlsGge.Atomic.KST006
open NlsGge.Atomic.KST012 NlsGge.Atomic.KST013
open NlsGge.Analysis NlsGge.Pilot
open NlsGge.GK38

def bcValues (n : ℤ) (b c : ℂ → ℂ) : Set ℝ :=
  {t | ∃ z ∈ spectralStrip n, t = ‖b z * c z‖}

def bcSup (n : ℤ) (b c : ℂ → ℂ) : ℝ := sSup (bcValues n b c)

theorem closedBall_subset_strip_of_le (n : ℤ) {r : ℝ} (hr : r ≤ Real.pi / 2) :
    Metric.closedBall (center n) r ⊆ spectralStrip n := by
  intro z hz
  simp only [spectralStrip, Set.mem_setOf_eq]
  have h1 : ‖z - center n‖ ≤ r := by
    simpa [dist_eq_norm] using Metric.mem_closedBall.1 hz
  have hre : (z - center n).re = z.re - (n : ℝ) * Real.pi := by simp [center]
  have h2 : |z.re - (n : ℝ) * Real.pi| ≤ ‖z - center n‖ := by
    have := Complex.abs_re_le_norm (z - center n)
    rwa [hre] at this
  linarith

theorem kst020 (n : ℤ) (a b c : ℂ → ℂ)
    (h : SmallCoefficients n a b c) (xp xm : ℂ)
    (hroots : Lib.zeroMultiset (determinant n a b c)
      (Metric.ball (center n) (Real.pi/3)) = {xp, xm}) :
  (∀ z ∈ Metric.closedBall (center n) (Real.pi/3),
    HasDerivAt a (deriv a z) z ∧ ‖deriv a z‖ ≤ (1/8 : ℝ)) ∧
  (bcValues n b c).Nonempty ∧ BddAbove (bcValues n b c) ∧
  ‖xp-xm‖ ≤ 3 * Real.sqrt (bcSup n b c) := by
  have hSC := h
  obtain ⟨ha, hb, hc, hbd⟩ := h
  have hπ := Real.pi_pos
  -- Cauchy estimate for the derivative of a
  have hderiv : ∀ z ∈ Metric.closedBall (center n) (Real.pi / 3),
      HasDerivAt a (deriv a z) z ∧ ‖deriv a z‖ ≤ (1 / 8 : ℝ) := by
    intro z hz
    have hball : Metric.closedBall z (Real.pi / 6) ⊆ spectralStrip n := by
      refine Set.Subset.trans ?_ (closedBall_subset_strip_of_le n (r := Real.pi / 2) (le_refl (Real.pi / 2)))
      intro w hw
      rw [Metric.mem_closedBall] at hw hz ⊢
      have := dist_triangle w z (center n)
      linarith
    have hA : AnalyticAt ℂ a z := ha z (hball (Metric.mem_closedBall_self (by positivity)))
    refine ⟨hA.differentiableAt.hasDerivAt, ?_⟩
    have hdiffOn : DifferentiableOn ℂ a (Metric.closedBall z (Real.pi / 6)) :=
      fun w hw => (ha w (hball hw)).differentiableAt.differentiableWithinAt
    have hd : DiffContOnCl ℂ a (Metric.ball z (Real.pi / 6)) :=
      ⟨hdiffOn.mono Metric.ball_subset_closedBall,
        hdiffOn.continuousOn.mono (by rw [closure_ball _ (by positivity)])⟩
    have hC : ∀ w ∈ Metric.sphere z (Real.pi / 6), ‖a w‖ ≤ Real.pi / 48 := fun w hw =>
      (hbd w (hball (Metric.sphere_subset_closedBall hw))).1
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hd hC
    calc ‖deriv a z‖ ≤ (Real.pi / 48) / (Real.pi / 6) := this
      _ = 1 / 8 := by field_simp; norm_num
  have hne : (bcValues n b c).Nonempty :=
    ⟨‖b (center n) * c (center n)‖, center n, by
      simp only [spectralStrip, Set.mem_setOf_eq]
      have : (center n).re = (n : ℝ) * Real.pi := by simp [center]
      rw [this, sub_self, abs_zero]; positivity, rfl⟩
  have hbdd : BddAbove (bcValues n b c) := by
    refine ⟨(Real.pi / 48) * (Real.pi / 48), ?_⟩
    rintro t ⟨z, hz, rfl⟩
    obtain ⟨-, hbb, hcb⟩ := hbd z hz
    calc ‖b z * c z‖ ≤ ‖b z‖ * ‖c z‖ := norm_mul_le _ _
      _ ≤ (Real.pi / 48) * (Real.pi / 48) :=
          mul_le_mul hbb hcb (norm_nonneg _) (by positivity)
  refine ⟨hderiv, hne, hbdd, ?_⟩
  -- the two roots
  obtain ⟨-, hnz, -⟩ := kst019 n a b c hSC
  have hgA : AnalyticOnNhd ℂ (determinant n a b c)
      (Metric.closedBall (center n) (Real.pi / 3)) := fun z hz => by
    have hz' := closedBall_subset_strip_of_le n (r := Real.pi / 3) (by linarith) hz
    exact (((analyticAt_id.sub analyticAt_const).sub (ha z hz')).pow 2).sub
      ((hb z hz').mul (hc z hz'))
  have hw : ∃ w ∈ Metric.closedBall (center n) (Real.pi / 3), determinant n a b c w ≠ 0 := by
    refine ⟨center n + ((Real.pi / 3 : ℝ) : ℂ), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      simp [abs_of_pos (show 0 < Real.pi / 3 by positivity)]
    · have hn : ‖center n + ((Real.pi / 3 : ℝ) : ℂ) - center n‖ = Real.pi / 3 := by
        simp [abs_of_pos (show 0 < Real.pi / 3 by positivity)]
      refine hnz _ ?_ (le_of_eq hn.symm)
      exact closedBall_subset_strip_of_le n (r := Real.pi / 3) (by linarith)
        (by rw [Metric.mem_closedBall, dist_eq_norm]; simp [abs_of_pos (show 0 < Real.pi / 3 by positivity)])
  have hzero : ∀ x ∈ Lib.zeroMultiset (determinant n a b c) (Metric.ball (center n) (Real.pi / 3)),
      x ∈ Metric.ball (center n) (Real.pi / 3) ∧ determinant n a b c x = 0 := fun x hx =>
    (NlsGge.GK38.Lib.mem_zeroMultiset_iff_zero hgA Metric.ball_subset_closedBall hw).1 hx
  have hxp := hzero xp (by rw [hroots]; simp)
  have hxm := hzero xm (by rw [hroots]; simp)
  have hbound : ∀ x, x ∈ Metric.ball (center n) (Real.pi / 3) → determinant n a b c x = 0 →
      ‖x - center n - a x‖ ≤ Real.sqrt (bcSup n b c) := by
    intro x hx hx0
    have hxs : x ∈ spectralStrip n :=
      closedBall_subset_strip_of_le n (r := Real.pi / 3) (by linarith) (Metric.ball_subset_closedBall hx)
    have h1 : (x - center n - a x) ^ 2 = b x * c x := by
      unfold determinant at hx0
      linear_combination hx0
    have h2 : ‖b x * c x‖ ≤ bcSup n b c := le_csSup hbdd ⟨x, hxs, rfl⟩
    have h3 : ‖x - center n - a x‖ ^ 2 ≤ bcSup n b c := by
      rw [← norm_pow, h1]; exact h2
    have := Real.abs_le_sqrt h3
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hmv : ‖a xp - a xm‖ ≤ (1 / 8 : ℝ) * ‖xp - xm‖ :=
    (convex_closedBall (center n) (Real.pi / 3)).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hderiv x hx).1.differentiableAt) (fun x hx => (hderiv x hx).2)
      (Metric.ball_subset_closedBall hxm.1) (Metric.ball_subset_closedBall hxp.1)
  have hsq0 : 0 ≤ Real.sqrt (bcSup n b c) := Real.sqrt_nonneg _
  have hdecomp : xp - xm = ((xp - center n - a xp) - (xm - center n - a xm)) + (a xp - a xm) := by
    ring
  have h4 : ‖xp - xm‖ ≤ ‖(xp - center n - a xp) - (xm - center n - a xm)‖ + ‖a xp - a xm‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  have h5 : ‖(xp - center n - a xp) - (xm - center n - a xm)‖ ≤
      ‖xp - center n - a xp‖ + ‖xm - center n - a xm‖ := norm_sub_le _ _
  have h6 := hbound xp hxp.1 hxp.2
  have h7 := hbound xm hxm.1 hxm.2
  linarith


end NlsGge.ThirdConsultation.KST
