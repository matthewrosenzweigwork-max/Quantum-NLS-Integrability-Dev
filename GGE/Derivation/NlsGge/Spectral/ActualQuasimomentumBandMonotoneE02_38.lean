import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38
import NlsGge.Spectral.ActualQuasimomentumLocalContinuationE02_38
import NlsGge.Spectral.ActualGapHeightSemicircleE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

theorem exists_monotoneOn_band_E02_38 (u : PhysicalL2) (x₀ : ℝ)
    (h : ‖actualPhysicalUnitHalfTrace32 u (x₀:ℂ)‖ < 1) :
    ∃ r > 0, MonotoneOn (actualQuasimomentumRealPartE02_38 u) (Set.Ioo (x₀ - r) (x₀ + r)) := by
  have hsq : actualPhysicalUnitHalfTrace32 u (x₀:ℂ) ^ 2 ≠ 1 := by
    intro h2
    have : ‖actualPhysicalUnitHalfTrace32 u (x₀:ℂ)‖ ^ 2 = 1 := by
      rw [← norm_pow, h2, norm_one]
    nlinarith [norm_nonneg (actualPhysicalUnitHalfTrace32 u (x₀:ℂ))]
  obtain ⟨r₁, hr₁, K, hK, hKk⟩ := exists_analytic_continuation_actualQuasimomentum_E02_38 u x₀ hsq
  have hΔc : Continuous (fun y : ℝ => actualPhysicalUnitHalfTrace32 u (y:ℂ)) :=
    (analyticOnNhd_actualPhysicalUnitHalfTrace32 u).continuousOn.comp_continuous
      Complex.continuous_ofReal (fun _ => Set.mem_univ _)
  have hev : ∀ᶠ y in 𝓝 (x₀:ℂ), ‖actualPhysicalUnitHalfTrace32 u y‖ < 1 :=
    (continuous_norm.continuousAt.comp
      ((analyticOnNhd_actualPhysicalUnitHalfTrace32 u).continuousOn.continuousAt
        Filter.univ_mem)).eventually (gt_mem_nhds h)
  obtain ⟨r₂, hr₂, hr₂'⟩ := Metric.eventually_nhds_iff.mp hev
  set r := min r₁ r₂ with hr
  have hrpos : 0 < r := lt_min hr₁ hr₂
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrr₂ : r ≤ r₂ := min_le_right _ _
  refine ⟨r, hrpos, ?_⟩
  have hmemB : ∀ y : ℝ, y ∈ Set.Ioo (x₀ - r) (x₀ + r) → (y:ℂ) ∈ Metric.ball (x₀:ℂ) r₁ := by
    intro y hy
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hmemΔ : ∀ y : ℝ, y ∈ Set.Ioo (x₀ - r) (x₀ + r) →
      ‖actualPhysicalUnitHalfTrace32 u (y:ℂ)‖ < 1 := by
    intro y hy
    apply hr₂'
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  -- boundary value equals K on the segment
  have hbd : ∀ y : ℝ, y ∈ Set.Ioo (x₀ - r) (x₀ + r) →
      actualQuasimomentumBoundaryE02_38 u y = K y := by
    intro y hy
    have hB := hmemB y hy
    have hne : (𝓝[{z : ℂ | 0 < z.im}] (y:ℂ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_upperHalfPlane_E02_38 (by simp))
    have h1 := tendsto_actualQuasimomentumBoundaryE02_38 u y
    have h2 : Tendsto K (𝓝[{z : ℂ | 0 < z.im}] (y:ℂ)) (𝓝 (K y)) :=
      ((hK.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hB)).tendsto).mono_left
        nhdsWithin_le_nhds
    have h3 : Tendsto (actualQuasimomentumE02_38 u) (𝓝[{z : ℂ | 0 < z.im}] (y:ℂ))
        (𝓝 (K y)) := by
      apply h2.congr'
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hB)] with z hz hzb
      exact hKk z hzb hz
    exact tendsto_nhds_unique h1 h3
  have hKim : ∀ y : ℝ, y ∈ Set.Ioo (x₀ - r) (x₀ + r) → (K y).im = 0 := by
    intro y hy
    have := boundaryLimit_im_E02_38 u y _ (tendsto_actualQuasimomentumBoundaryE02_38 u y)
    rw [hbd y hy] at this
    rw [this]
    exact (actualGapHeightE02_38_eq_zero_iff u y).mpr (hmemΔ y hy).le
  -- derivative nonneg
  have hder : ∀ y : ℝ, y ∈ Set.Ioo (x₀ - r) (x₀ + r) → 0 ≤ (deriv K (y:ℂ)).re := by
    intro y hy
    have hB := hmemB y hy
    have hKd : HasDerivAt K (deriv K (y:ℂ)) (y:ℂ) :=
      ((hK (y:ℂ) hB).differentiableAt).hasDerivAt
    have hlin : HasDerivAt (fun w : ℂ => (y:ℂ) + Complex.I * w) Complex.I ((0:ℝ):ℂ) := by
      simpa using ((hasDerivAt_id ((0:ℝ):ℂ)).const_mul Complex.I).const_add (y:ℂ)
    have hcomp : HasDerivAt (fun w : ℂ => K ((y:ℂ) + Complex.I * w))
        (deriv K (y:ℂ) * Complex.I) ((0:ℝ):ℂ) := by
      have hKd' : HasDerivAt K (deriv K (y:ℂ)) ((y:ℂ) + Complex.I * ((0:ℝ):ℂ)) := by
        simpa using hKd
      have := HasDerivAt.comp (((0:ℝ):ℂ)) hKd' hlin
      simpa [Function.comp_def] using this
    have hφ : HasDerivAt (fun t : ℝ => K ((y:ℂ) + Complex.I * (t:ℂ)))
        (deriv K (y:ℂ) * Complex.I) 0 := hcomp.comp_ofReal
    have hg : HasDerivAt (fun t : ℝ => (K ((y:ℂ) + Complex.I * (t:ℂ))).im)
        (deriv K (y:ℂ) * Complex.I).im 0 :=
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) hφ)
    have himI : (deriv K (y:ℂ) * Complex.I).im = (deriv K (y:ℂ)).re := by simp
    rw [himI] at hg
    have hslope := hg.tendsto_slope_zero_right
    have hg0 : (K ((y:ℂ) + Complex.I * ((0:ℝ):ℂ))).im = 0 := by
      simpa using hKim y hy
    apply ge_of_tendsto hslope
    have hδ : 0 < min (y - (x₀ - r)) (x₀ + r - y) := lt_min (by linarith [hy.1]) (by linarith [hy.2])
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    have htpos : 0 < t := ht.1
    have hz : 0 < ((y:ℂ) + Complex.I * (t:ℂ)).im := by simpa using htpos
    have hzB : ((y:ℂ) + Complex.I * (t:ℂ)) ∈ Metric.ball (x₀:ℂ) r₁ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : (y:ℂ) + Complex.I * (t:ℂ) - (x₀:ℂ) = ((y - x₀ : ℝ):ℂ) + Complex.I * (t:ℂ) := by
        push_cast; ring
      rw [this]
      refine lt_of_le_of_lt (norm_add_le _ _) ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htpos]
      have h1 := ht.2
      have h2 := min_le_left (y - (x₀ - r)) (x₀ + r - y)
      have h3 := min_le_right (y - (x₀ - r)) (x₀ + r - y)
      have hlt : |y - x₀| + t < r := by
        rcases le_total 0 (y - x₀) with hh | hh
        · rw [abs_of_nonneg hh]; linarith
        · rw [abs_of_nonpos hh]; linarith
      linarith
    have hpos : 0 < (K ((y:ℂ) + Complex.I * (t:ℂ))).im := by
      rw [hKk _ hzB hz]
      exact (isActualQuasimomentumBranch_actualQuasimomentumE02_38 u).2.2.1 _ hz
    simp only [zero_add, smul_eq_mul]
    rw [hg0] at *
    simp only [sub_zero] at *
    exact (mul_pos (inv_pos.mpr htpos) hpos).le
  -- real function
  set P : ℝ → ℝ := fun x => (K (x:ℂ)).re with hP
  have hPd : ∀ y : ℝ, y ∈ Set.Ioo (x₀ - r) (x₀ + r) →
      HasDerivAt P (deriv K (y:ℂ)).re y := by
    intro y hy
    have hKd : HasDerivAt K (deriv K (y:ℂ)) (y:ℂ) :=
      ((hK (y:ℂ) (hmemB y hy)).differentiableAt).hasDerivAt
    exact hKd.real_of_complex
  have hmono : MonotoneOn P (Set.Ioo (x₀ - r) (x₀ + r)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
    · intro y hy; exact (hPd y (by simpa using hy)).continuousAt.continuousWithinAt
    · intro y hy; rw [interior_Ioo] at hy; exact (hPd y hy).differentiableAt.differentiableWithinAt
    · intro y hy; rw [interior_Ioo] at hy; rw [(hPd y hy).deriv]; exact hder y hy
  intro a ha b hb hab
  have := hmono ha hb hab
  simp only [actualQuasimomentumRealPartE02_38, hbd a ha, hbd b hb]
  exact this


end NlsGge.SpectralFoundations
end
