import Mathlib

namespace NlsGge.Atomic.AL034


                                                                                                                                            
set_option autoImplicit false

theorem AL034_radial (a : ℝ) (ha : 0 < a) :
    ∫ y in (0 : ℝ)..1, y * (1 - y ^ 2) ^ (a - 1) = 1 / (2 * a) := by
  let F : ℝ → ℝ := fun y => -((1 - y ^ 2) ^ a) / (2 * a)
  have hFc : Continuous F := by
    have : Continuous (fun y : ℝ => (1 - y ^ 2) ^ a) :=
      (Real.continuous_rpow_const ha.le).comp (by fun_prop)
    exact this.neg.div_const _
  have hFd : ∀ y ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (y * (1 - y ^ 2) ^ (a - 1)) y := by
    intro y hy
    have hne : 1 - y ^ 2 ≠ 0 := by nlinarith [hy.1, hy.2]
    have hbase : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * y)) y := by
      simpa using ((hasDerivAt_id y).pow 2).const_sub 1
    have h := ((hbase.rpow_const (p := a) (Or.inl hne)).neg).div_const (2 * a)
    convert h using 1
    field_simp
  have hpos : ∀ y ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ y * (1 - y ^ 2) ^ (a - 1) := by
    intro y hy
    have : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    exact mul_nonneg hy.1.le (Real.rpow_nonneg this.le _)
  have hint : IntervalIntegrable (fun y : ℝ => y * (1 - y ^ 2) ^ (a - 1)) MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.integrableOn_deriv_of_nonneg hFc.continuousOn hFd hpos
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hFc.continuousOn hFd hint]
  simp only [F]
  rw [show ((1 : ℝ) - 1 ^ 2) = 0 by norm_num, show ((1 : ℝ) - 0 ^ 2) = 1 by norm_num,
    Real.zero_rpow ha.ne', Real.one_rpow]
  ring

theorem AL034_main : ((∀ a : ℝ, 0 < a → ∫ z in Metric.ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) ^ (a - 1) = Real.pi / a) : Prop) := by
  intro a ha
  set f : ℝ → ℝ := fun y => if y < 1 then (1 - y ^ 2) ^ (a - 1) else 0 with hf
  have hz : ∀ z : ℂ, (Metric.ball (0 : ℂ) 1).indicator (fun z : ℂ => (1 - ‖z‖ ^ 2) ^ (a - 1)) z = f ‖z‖ := by
    intro z
    by_cases h : ‖z‖ < 1
    · simp [Set.indicator, h, hf]
    · simp [Set.indicator, h, hf]
  have h1 : ∫ z in Metric.ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) ^ (a - 1) = ∫ z : ℂ, f ‖z‖ := by
    rw [← MeasureTheory.integral_indicator Metric.isOpen_ball.measurableSet]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hz)
  rw [h1, MeasureTheory.integral_fun_norm_addHaar MeasureTheory.volume f]
  have hvol : MeasureTheory.volume.real (Metric.ball (0 : ℂ) 1) = Real.pi := by
    rw [MeasureTheory.measureReal_def, Complex.volume_ball]
    simp
  have hrad : ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • f y = 1 / (2 * a) := by
    rw [Complex.finrank_real_complex]
    have hset : ∫ y in Set.Ioi (0 : ℝ), y ^ (2 - 1) • f y = ∫ y in Set.Ioc (0 : ℝ) 1, y ^ (2 - 1) • f y := by
      refine MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
        Set.Ioc_subset_Ioi_self ?_
      intro y hy
      have : ¬ y < 1 := by
        intro h
        exact hy.2 ⟨hy.1, h.le⟩
      simp [hf, this]
    rw [hset, ← intervalIntegral.integral_of_le zero_le_one]
    have hcongr : ∫ y in (0 : ℝ)..1, y ^ (2 - 1) • f y = ∫ y in (0 : ℝ)..1, y * (1 - y ^ 2) ^ (a - 1) := by
      have h1ne : ∀ᵐ y : ℝ ∂MeasureTheory.volume, y ≠ 1 := by
        rw [MeasureTheory.ae_iff]; simp
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [h1ne] with y hy1 hmem
      rw [Set.uIoc_of_le zero_le_one] at hmem
      have hlt : y < 1 := lt_of_le_of_ne hmem.2 hy1
      simp [hf, hlt]
    rw [hcongr]
    exact AL034_radial a ha
  rw [hrad, hvol, Complex.finrank_real_complex]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  field_simp


end NlsGge.Atomic.AL034
