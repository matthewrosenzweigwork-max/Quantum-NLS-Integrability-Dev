import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.Spectral.ActualQuasimomentumMonotoneE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- `cosh d - 1 ≥ d²/2` for `d ≥ 0`. -/
theorem cosh_sub_one_ge_E02_38 (d : ℝ) (hd : 0 ≤ d) : d ^ 2 / 2 ≤ Real.cosh d - 1 := by
  have h1 : d / 2 ≤ Real.sinh (d / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  have h2 : Real.cosh d = 1 + 2 * Real.sinh (d / 2) ^ 2 := by
    have := Real.cosh_two_mul (d / 2)
    have h3 := Real.cosh_sq (d / 2)
    rw [show 2 * (d / 2) = d by ring] at this
    nlinarith
  have h0 : 0 ≤ d / 2 := by linarith
  nlinarith [mul_le_mul h1 h1 h0 (le_trans h0 h1)]

theorem arcosh_holder_aux_E02_38 (y y' : ℝ) (hy' : 1 ≤ y') (h : y' ≤ y) :
    Real.arcosh y - Real.arcosh y' ≤ Real.sqrt (2 * |y - y'|) := by
  have hy : 1 ≤ y := le_trans hy' h
  set a := Real.arcosh y with ha
  set b := Real.arcosh y' with hb
  have hb0 : 0 ≤ b := Real.arcosh_nonneg hy'
  have hba : b ≤ a := by
    rw [ha, hb]
    exact (Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr h
  have hca : Real.cosh a = y := Real.cosh_arcosh hy
  have hcb : Real.cosh b = y' := Real.cosh_arcosh hy'
  have hd := cosh_sub_one_ge_E02_38 (a - b) (by linarith)
  have hsub : Real.cosh a = Real.cosh b * Real.cosh (a - b) + Real.sinh b * Real.sinh (a - b) := by
    have := Real.cosh_add b (a - b)
    rw [show b + (a - b) = a by ring] at this
    exact this
  have hsb : 0 ≤ Real.sinh b := Real.sinh_nonneg_iff.mpr hb0
  have hsd : 0 ≤ Real.sinh (a - b) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hc1 : 1 ≤ Real.cosh (a - b) := Real.one_le_cosh _
  have hcb1 : 1 ≤ Real.cosh b := Real.one_le_cosh _
  have key : (a - b) ^ 2 ≤ 2 * (y - y') := by
    have : Real.cosh a - Real.cosh b ≥ Real.cosh (a - b) - 1 := by
      rw [hsub]
      nlinarith [mul_nonneg hsb hsd, mul_nonneg (sub_nonneg.mpr hcb1) (sub_nonneg.mpr hc1)]
    rw [hca, hcb] at this
    linarith
  have : (a - b) ^ 2 ≤ 2 * |y - y'| := by
    have := le_abs_self (y - y'); linarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt this)

/-- (1) Hölder-1/2 continuity of `arcosh` on `[1, ∞)`. -/
theorem arcosh_holder_E02_38 : ∀ y y' : ℝ, 1 ≤ y → 1 ≤ y' →
    |Real.arcosh y - Real.arcosh y'| ≤ Real.sqrt (2 * |y - y'|) := by
  intro y y' hy hy'
  rcases le_total y' y with h | h
  · rw [abs_of_nonneg (by
      have := (Real.arcosh_le_arcosh (by linarith : (0:ℝ) < y') (by linarith : (0:ℝ) < y)).mpr h
      linarith)]
    exact arcosh_holder_aux_E02_38 y y' hy' h
  · rw [abs_sub_comm, abs_sub_comm y y']
    rw [abs_of_nonneg (by
      have := (Real.arcosh_le_arcosh (by linarith : (0:ℝ) < y) (by linarith : (0:ℝ) < y')).mpr h
      linarith)]
    exact arcosh_holder_aux_E02_38 y' y hy h

/-- (2) Local Hölder-1/2 continuity of the gap height. -/
theorem actualGapHeight_holder_E02_38 (u : PhysicalL2) (A : ℝ) :
    ∃ H : ℝ, ∀ s ∈ Set.Icc (-A) A, ∀ t ∈ Set.Icc (-A) A,
      |actualGapHeightE02_38 u s - actualGapHeightE02_38 u t| ≤ H * Real.sqrt |s - t| := by
  have hd : Differentiable ℂ (actualPhysicalUnitHalfTrace32 u) := fun z =>
    ((analyticOnNhd_actualPhysicalUnitHalfTrace32 u) z (Set.mem_univ _)).differentiableAt
  have hC : ContDiff ℝ 1 (fun x : ℝ => actualPhysicalUnitHalfTrace32 u (x : ℂ)) := by
    have h1 : ContDiff ℂ 1 (actualPhysicalUnitHalfTrace32 u) := hd.contDiff
    exact (h1.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  obtain ⟨K, hK⟩ := hC.contDiffOn.exists_lipschitzOnWith (s := Set.Icc (-A) A) one_ne_zero
    (convex_Icc _ _) isCompact_Icc
  refine ⟨Real.sqrt (2 * K), fun s hs t ht => ?_⟩
  set g : ℝ → ℝ := fun x => max 1 ‖actualPhysicalUnitHalfTrace32 u (x : ℂ)‖ with hg
  have h1 : |g s - g t| ≤ |‖actualPhysicalUnitHalfTrace32 u (s : ℂ)‖ -
      ‖actualPhysicalUnitHalfTrace32 u (t : ℂ)‖| := by
    simp only [hg]
    set a := ‖actualPhysicalUnitHalfTrace32 u (s : ℂ)‖
    set b := ‖actualPhysicalUnitHalfTrace32 u (t : ℂ)‖
    rw [max_comm 1 a, max_comm 1 b]
    exact abs_max_sub_max_le_abs a b 1
  have h2 : |‖actualPhysicalUnitHalfTrace32 u (s : ℂ)‖ -
      ‖actualPhysicalUnitHalfTrace32 u (t : ℂ)‖| ≤ K * |s - t| := by
    have := hK.dist_le_mul s hs t ht
    rw [dist_eq_norm, Real.dist_eq] at this
    exact (abs_norm_sub_norm_le _ _).trans this
  have h3 := arcosh_holder_E02_38 (g s) (g t) (le_max_left _ _) (le_max_left _ _)
  have h4 : Real.sqrt (2 * |g s - g t|) ≤ Real.sqrt (2 * (K * |s - t|)) :=
    Real.sqrt_le_sqrt (by linarith)
  have h5 : Real.sqrt (2 * (K * |s - t|)) = Real.sqrt (2 * K) * Real.sqrt |s - t| := by
    rw [← Real.sqrt_mul (by
      have := hK.dist_le_mul s hs s hs
      positivity)]
    ring_nf
  show |Real.arcosh (g s) - Real.arcosh (g t)| ≤ _
  linarith


/-- `p x ∈ πℤ` whenever `|Δh x| > 1`. -/
theorem quasimomentum_re_int_of_gap_E02_38 (u : PhysicalL2) (y : ℝ)
    (hy : 1 < ‖actualPhysicalUnitHalfTrace32 u (y:ℂ)‖) :
    ∃ n : ℤ, actualQuasimomentumRealPartE02_38 u y = (n:ℝ) * Real.pi := by
  have hcos := actualQuasimomentumBoundaryE02_38_cos u y
  have him : (Complex.cos (actualQuasimomentumBoundaryE02_38 u y)).im = 0 := by
    rw [hcos]; exact actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 u y
  rw [complex_cos_im_E02_38] at him
  have hv : actualGapHeightE02_38 u y ≠ 0 := by
    rw [Ne, actualGapHeightE02_38_eq_zero_iff]
    exact not_le.mpr hy
  have hLim : (actualQuasimomentumBoundaryE02_38 u y).im = actualGapHeightE02_38 u y :=
    boundaryLimit_im_E02_38 u y _ (tendsto_actualQuasimomentumBoundaryE02_38 u y)
  have hsinh : Real.sinh (actualQuasimomentumBoundaryE02_38 u y).im ≠ 0 := by
    rw [hLim]; exact fun h => hv (Real.sinh_eq_zero.mp h)
  have hsin : Real.sin (actualQuasimomentumBoundaryE02_38 u y).re = 0 := by
    have : Real.sin (actualQuasimomentumBoundaryE02_38 u y).re *
        Real.sinh (actualQuasimomentumBoundaryE02_38 u y).im = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hsinh
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  exact ⟨n, by simp only [actualQuasimomentumRealPartE02_38]; exact hn.symm⟩

theorem actualGapHeight_mem_gap_of_ne_zero_E02_38 (u : PhysicalL2) (x : ℝ)
    (hx : actualGapHeightE02_38 u x ≠ 0) :
    ∃ n : ℤ, x ∈ Set.Ioo (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
  have h1 : 1 < ‖actualPhysicalUnitHalfTrace32 u (x:ℂ)‖ := by
    rw [Ne, actualGapHeightE02_38_eq_zero_iff, not_le] at hx
    exact hx
  obtain ⟨n, hn⟩ := quasimomentum_re_int_of_gap_E02_38 u x h1
  obtain ⟨r, hr, hc⟩ := exists_const_near_gap_E02_38 u x h1
  have hset := (actualGapLevelSet_eq_Icc_E02_38 u n).2
  have hmem : ∀ y ∈ Set.Ioo (x - r) (x + r),
      y ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
    intro y hy
    rw [← hset]
    show actualQuasimomentumRealPartE02_38 u y = (n:ℝ) * Real.pi
    rw [hc y hy, hn]
  refine ⟨n, ?_, ?_⟩
  · exact lt_of_le_of_lt (hmem (x - r/2) ⟨by linarith, by linarith⟩).1 (by linarith)
  · exact lt_of_lt_of_le (by linarith) (hmem (x + r/2) ⟨by linarith, by linarith⟩).2

/-- (3) Support of `v` in the finitely many open gaps, and compact support. -/
theorem actualGapHeight_support_finiteGap_E02_38 (u : PhysicalL2)
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite) :
    (∀ x : ℝ, actualGapHeightE02_38 u x ≠ 0 →
      ∃ n : ℤ, x ∈ Set.Ioo (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)) ∧
    ∃ A : ℝ, ∀ x : ℝ, A < |x| → actualGapHeightE02_38 u x = 0 := by
  refine ⟨actualGapHeight_mem_gap_of_ne_zero_E02_38 u, ?_⟩
  have hb : Bornology.IsBounded (⋃ n ∈ {n : ℤ | actualGapLowerAllE02_38 u n <
      actualGapUpperAllE02_38 u n}, Set.Ioo (actualGapLowerAllE02_38 u n)
        (actualGapUpperAllE02_38 u n)) :=
    (Bornology.isBounded_biUnion hfin).2 (fun n _ => Metric.isBounded_Ioo _ _)
  obtain ⟨A, hA⟩ := hb.subset_closedBall (0:ℝ)
  refine ⟨A, fun x hx => ?_⟩
  by_contra hne
  obtain ⟨n, hn⟩ := actualGapHeight_mem_gap_of_ne_zero_E02_38 u x hne
  have hlt : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n := hn.1.trans hn.2
  have : x ∈ Metric.closedBall (0:ℝ) A := hA (Set.mem_biUnion hlt hn)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith

/-- (4) Integral formula. -/
theorem actualGapHeight_integral_eq_sum_E02_38 (u : PhysicalL2)
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite)
    (f : ℝ → ℝ) (hf : Continuous f) :
    MeasureTheory.Integrable (fun l : ℝ =>
        f (actualQuasimomentumRealPartE02_38 u l) * actualGapHeightE02_38 u l) ∧
    ∫ l : ℝ, f (actualQuasimomentumRealPartE02_38 u l) * actualGapHeightE02_38 u l =
      ∑ n ∈ hfin.toFinset, f ((n:ℝ) * Real.pi) *
        ∫ l in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
          actualGapHeightE02_38 u l := by
  set F := hfin.toFinset with hF
  have hv : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have hlev : ∀ n : ℤ, ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      actualQuasimomentumRealPartE02_38 u x = (n:ℝ) * Real.pi := by
    intro n x hx
    have := (actualGapLevelSet_eq_Icc_E02_38 u n).2
    rw [← this] at hx
    exact hx
  have hpt : ∀ l : ℝ, f (actualQuasimomentumRealPartE02_38 u l) * actualGapHeightE02_38 u l =
      ∑ n ∈ F, (Set.Ioo (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)).indicator
        (fun l => f ((n:ℝ) * Real.pi) * actualGapHeightE02_38 u l) l := by
    intro l
    by_cases h0 : actualGapHeightE02_38 u l = 0
    · rw [h0]; simp only [mul_zero]
      symm; apply Finset.sum_eq_zero; intro n _
      apply Set.indicator_apply_eq_zero.mpr; intro _; simp [h0]
    · obtain ⟨n0, hn0⟩ := actualGapHeight_mem_gap_of_ne_zero_E02_38 u l h0
      have hn0F : n0 ∈ F := by
        rw [hF, Set.Finite.mem_toFinset]; exact hn0.1.trans hn0.2
      rw [Finset.sum_eq_single n0]
      · rw [Set.indicator_of_mem hn0, hlev n0 l ⟨hn0.1.le, hn0.2.le⟩]
      · intro m _ hm
        apply Set.indicator_of_notMem
        intro hmem
        have h1 := hlev n0 l ⟨hn0.1.le, hn0.2.le⟩
        have h2 := hlev m l ⟨hmem.1.le, hmem.2.le⟩
        have : (n0:ℝ) = m := by
          have := h1.symm.trans h2
          exact mul_right_cancel₀ Real.pi_ne_zero this
        exact hm (by exact_mod_cast this.symm)
      · intro h; exact absurd hn0F h
  have hint : ∀ n ∈ F, MeasureTheory.Integrable
      ((Set.Ioo (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)).indicator
        (fun l => f ((n:ℝ) * Real.pi) * actualGapHeightE02_38 u l)) := by
    intro n _
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact ((continuous_const.mul hv).continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have heq : (fun l : ℝ => f (actualQuasimomentumRealPartE02_38 u l) * actualGapHeightE02_38 u l)
      = fun l => ∑ n ∈ F, (Set.Ioo (actualGapLowerAllE02_38 u n)
          (actualGapUpperAllE02_38 u n)).indicator
        (fun l => f ((n:ℝ) * Real.pi) * actualGapHeightE02_38 u l) l := funext hpt
  rw [heq]
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hlt : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n := by
    rw [hF, Set.Finite.mem_toFinset] at hn; exact hn
  rw [integral_indicator measurableSet_Ioo, integral_const_mul,
    intervalIntegral.integral_of_le hlt.le, integral_Ioc_eq_integral_Ioo]

end NlsGge.SpectralFoundations
