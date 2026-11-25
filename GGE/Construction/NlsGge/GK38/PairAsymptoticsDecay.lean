import NlsGge.GK38.PairAsymptoticsIntegrationByParts

/-! # F5: uniform weighted oscillatory decay (GK Appendix D.1) -/

set_option autoImplicit false

open Filter Topology MeasureTheory Set
open scoped ContDiff

namespace NlsGge.GK38

noncomputable section

open NlsGge.Pilot

theorem integral_osc_smooth_decay (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    {ε : ℝ} (hε : 0 < ε) : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * g s‖ ≤
          ε * Real.exp (|z.im| * t) := by
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuous.continuousOn
  let C : ℝ := 2 * A + ∫ s : ℝ in 0..1, ‖deriv g s‖
  refine ⟨max 1 (C / ε), fun z hz t ht => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hz
  have hCz : C ≤ (2 * ‖z‖) * ε := by
    have hc := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hz)
    nlinarith [norm_nonneg z]
  have hp : 0 < 2 * ‖z‖ := by linarith
  apply (mul_le_mul_iff_right₀ hp).mp
  exact (norm_integral_osc_smooth_mul_le g hg A hA z ht).trans
    (by
      change C * Real.exp (|z.im| * t) ≤ _
      calc C * Real.exp (|z.im| * t) ≤ ((2 * ‖z‖) * ε) * Real.exp (|z.im| * t) :=
            mul_le_mul_of_nonneg_right hCz (Real.exp_nonneg _)
        _ = _ := by ring)

/-- Weighted Riemann–Lebesgue decay, uniform in time and complex frequency. -/
theorem integral_osc_decay (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * f s‖ ≤
          ε * Real.exp (|z.im| * t) := by
  obtain ⟨g, hg, hfg⟩ := exists_smooth_l1_approx38 f hf (half_pos hε)
  obtain ⟨R, hR⟩ := integral_osc_smooth_decay g hg (half_pos hε)
  refine ⟨R, fun z hz t ht => ?_⟩
  have hsub : IntervalIntegrable (fun s => f s - g s) volume 0 1 :=
    hf.sub (hg.continuous.intervalIntegrable _ _)
  have hI := norm_integral_osc_le (fun s => f s - g s) hsub z ht
  have hG := hR z hz t ht
  have heq : (∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * f s) =
      (∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * (f s - g s)) +
      ∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * g s := by
    rw [← intervalIntegral.integral_add (intervalIntegrable_osc _ hsub z ht)
      (intervalIntegrable_osc _ (hg.continuous.intervalIntegrable _ _) z ht)]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  have hI' := hI.trans (mul_le_mul_of_nonneg_left hfg (Real.exp_nonneg _))
  convert add_le_add hI' hG using 1 <;> ring

/-- The oscillatory functional respects the a.e. representatives of potential differences. -/
theorem integral_osc_cover_sub (f g : PhysicalL2) (z : ℂ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * coverRep38 f s) -
      (∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * coverRep38 g s) =
    ∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * coverRep38 (f - g) s := by
  have hf := intervalIntegrable_osc _ (intervalIntegrable_coverRep38_one f) z ht
  have hg := intervalIntegrable_osc _ (intervalIntegrable_coverRep38_one g) z ht
  have hdiff := intervalIntegrable_osc _ (intervalIntegrable_coverRep38_one (f - g)) z ht
  rw [← intervalIntegral.integral_sub hf hg]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [coverRep38_sub_ae f g] with s hs
  intro _
  simp only [hs, mul_sub]

/-- Appendix D.1 with explicit local uniformity in the L2 potential. -/
theorem integral_osc_cover_decay (f₀ : PhysicalL2) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ f : PhysicalL2, ‖f - f₀‖ ≤ ε / 2 → ∀ z : ℂ, R ≤ ‖z‖ →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * coverRep38 f s‖ ≤
          ε * Real.exp (|z.im| * t) := by
  obtain ⟨R, hR⟩ := integral_osc_decay (coverRep38 f₀)
    (intervalIntegrable_coverRep38_one f₀) (half_pos hε)
  refine ⟨R, fun f hf z hz t ht => ?_⟩
  have hb := norm_integral_osc_le (coverRep38 (f - f₀))
    (intervalIntegrable_coverRep38_one _) z ht
  have hb' := hb.trans (mul_le_mul_of_nonneg_left
    ((integral_coverRep38_le_one (f - f₀)).trans hf) (Real.exp_nonneg _))
  have heq := integral_osc_cover_sub f f₀ z ht
  have h0 := hR z hz t ht
  have htri := norm_add_le
    (∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * coverRep38 (f - f₀) s)
    (∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * coverRep38 f₀ s)
  have hsum : (∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * coverRep38 f s) =
      (∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * coverRep38 (f - f₀) s) +
      (∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * coverRep38 f₀ s) := by
    linear_combination heq
  rw [hsum]
  refine htri.trans ?_
  convert add_le_add hb' h0 using 1 <;> ring

end

end NlsGge.GK38
