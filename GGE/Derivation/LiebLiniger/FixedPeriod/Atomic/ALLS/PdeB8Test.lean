import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB7Approved

/-! # Track B, contract 6 preparation: calculus and Fourier series of spacetime test functions

For a test function `φ` of the approved `IsSpacetimeTest` class:
* `Dx φ`, `Dt φ` (partial derivatives, as the `deriv` expressions occurring in the approved
  `IsDistributionalNLS`) are again test functions; `iteratedDeriv 2` in `x` is `Dx (Dx φ)`;
* test functions are bounded;
* `cT φ m t = ∫₀¹ e^{-2πimx} φ(t,x) dx` satisfies `cT (Dx φ) m t = 2πim cT φ m t`,
  `‖cT φ m t‖ ≤ K/(1+(2πm)²)` uniformly in `t`, `∑ₘ cT φ m t e^{2πimx} = φ(t,x)` (pointwise
  Fourier series, Mathlib `has_pointwise_sum_fourier_series_of_summable`) and
  `d/dt cT φ m t = cT (Dt φ) m t` (differentiation under the integral sign).
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

/-- Partial derivative in `x`. -/
def Dx (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := deriv (fun y => φ (p.1, y)) p.2

/-- Partial derivative in `t`. -/
def Dt (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := deriv (fun s => φ (s, p.2)) p.1

theorem hasDerivAt_x_fderiv {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (t x : ℝ) :
    HasDerivAt (fun y => φ (t, y)) (fderiv ℝ φ (t, x) ((0 : ℝ), (1 : ℝ))) x := by
  have h1 : HasDerivAt (fun y : ℝ => ((t, y) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
  have h2 := ((hφ.differentiable (by simp)) (t, x)).hasFDerivAt
  exact h2.comp_hasDerivAt x h1

theorem hasDerivAt_t_fderiv {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (t x : ℝ) :
    HasDerivAt (fun s => φ (s, x)) (fderiv ℝ φ (t, x) ((1 : ℝ), (0 : ℝ))) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s, x) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have h2 := ((hφ.differentiable (by simp)) (t, x)).hasFDerivAt
  exact h2.comp_hasDerivAt t h1

theorem hasDerivAt_Dx {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (t x : ℝ) :
    HasDerivAt (fun y => φ (t, y)) (Dx φ (t, x)) x :=
  (hasDerivAt_x_fderiv hφ t x).differentiableAt.hasDerivAt

theorem hasDerivAt_Dt {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (t x : ℝ) :
    HasDerivAt (fun s => φ (s, x)) (Dt φ (t, x)) t :=
  (hasDerivAt_t_fderiv hφ t x).differentiableAt.hasDerivAt

theorem Dx_eq_fderiv {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    Dx φ = fun p => fderiv ℝ φ p ((0 : ℝ), (1 : ℝ)) := by
  funext p
  exact (hasDerivAt_x_fderiv hφ p.1 p.2).deriv

theorem Dt_eq_fderiv {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    Dt φ = fun p => fderiv ℝ φ p ((1 : ℝ), (0 : ℝ)) := by
  funext p
  exact (hasDerivAt_t_fderiv hφ p.1 p.2).deriv

theorem contDiff_fderiv_apply {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
  (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem iteratedDeriv_two_eq (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    iteratedDeriv 2 (fun y => φ (p.1, y)) p.2 = Dx (Dx φ) p := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  rfl

theorem deriv_t_eq (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    deriv (fun s => φ (s, p.2)) p.1 = Dt φ p := rfl

namespace IsSpacetimeTest

variable {φ ψ : ℝ × ℝ → ℂ}

theorem dx (hφ : IsSpacetimeTest φ) : IsSpacetimeTest (Dx φ) where
  smooth := by
    rw [Dx_eq_fderiv hφ.smooth]
    exact contDiff_fderiv_apply hφ.smooth _
  periodic := by
    intro t x
    have hf : (fun y => φ (t, y + 1)) = fun y => φ (t, y) := funext fun y => hφ.periodic t y
    simp only [Dx]
    rw [← deriv_comp_add_const, hf]
  compact_time := by
    obtain ⟨T, hT⟩ := hφ.compact_time
    refine ⟨T, fun t x ht => ?_⟩
    have hf : (fun y => φ (t, y)) = fun _ => (0 : ℂ) := funext fun y => hT t y ht
    simp only [Dx]
    rw [hf, deriv_const]

theorem dt (hφ : IsSpacetimeTest φ) : IsSpacetimeTest (Dt φ) where
  smooth := by
    rw [Dt_eq_fderiv hφ.smooth]
    exact contDiff_fderiv_apply hφ.smooth _
  periodic := by
    intro t x
    have hf : (fun s => φ (s, x + 1)) = fun s => φ (s, x) := funext fun s => hφ.periodic s x
    simp only [Dt]
    rw [hf]
  compact_time := by
    obtain ⟨T, hT⟩ := hφ.compact_time
    refine ⟨T, fun t x ht => ?_⟩
    have hev : (fun s => φ (s, x)) =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
      have hopen : IsOpen {s : ℝ | T < |s|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hopen.mem_nhds ht] with s hs
      exact hT s x hs
    simp only [Dt]
    rw [hev.deriv_eq, deriv_const]

theorem sub_smul (hφ : IsSpacetimeTest φ) (hψ : IsSpacetimeTest ψ) (c : ℂ) :
    IsSpacetimeTest (fun p => φ p - c * ψ p) where
  smooth := hφ.smooth.sub (contDiff_const.mul hψ.smooth)
  periodic := fun t x => by rw [hφ.periodic, hψ.periodic]
  compact_time := by
    obtain ⟨T, hT⟩ := hφ.compact_time
    obtain ⟨T', hT'⟩ := hψ.compact_time
    refine ⟨max T T', fun t x ht => ?_⟩
    rw [hT t x (lt_of_le_of_lt (le_max_left _ _) ht), hT' t x (lt_of_le_of_lt (le_max_right _ _) ht),
      mul_zero, sub_zero]

theorem continuous (hφ : IsSpacetimeTest φ) : Continuous φ := hφ.smooth.continuous

theorem eq_fract (hφ : IsSpacetimeTest φ) (t x : ℝ) : φ (t, x) = φ (t, Int.fract x) := by
  have hper : Function.Periodic (fun y => φ (t, y)) 1 := fun y => hφ.periodic t y
  have h := (hper.int_mul ⌊x⌋) (Int.fract x)
  simp only [mul_one, Int.fract_add_floor] at h
  exact h

theorem bounded (hφ : IsSpacetimeTest φ) : ∃ B, 0 ≤ B ∧ ∀ p, ‖φ p‖ ≤ B := by
  obtain ⟨T, hT⟩ := hφ.compact_time
  have hK : IsCompact (Set.Icc (-|T|) |T| ×ˢ Set.Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun p => ?_⟩
  obtain ⟨t, x⟩ := p
  by_cases ht : T < |t|
  · rw [hT t x ht, norm_zero]
    exact le_max_right _ _
  · rw [hφ.eq_fract t x]
    refine (hC _ ⟨⟨?_, ?_⟩, ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩⟩).trans (le_max_left _ _)
    · have := neg_abs_le t
      have := le_abs_self T
      rw [not_lt] at ht
      have := abs_le.mp (ht.trans (le_abs_self T))
      linarith [this.1]
    · rw [not_lt] at ht
      have := abs_le.mp (ht.trans (le_abs_self T))
      exact this.2

end IsSpacetimeTest

/-! ### Fourier coefficients on `[0,1]` -/

/-- The character `x ↦ e^{2πimx}` on `ℝ`. -/
def ex (m : ℤ) (x : ℝ) : ℂ := fourier m (x : PhysicalCircle)

theorem norm_ex (m : ℤ) (x : ℝ) : ‖ex m x‖ = 1 := norm_fourier_apply _ _

theorem continuous_ex (m : ℤ) : Continuous (ex m) :=
  (map_continuous (fourier m)).comp continuous_quotient_mk'

theorem hasDerivAt_ex (m : ℤ) (x : ℝ) :
    HasDerivAt (ex m) (2 * Real.pi * Complex.I * m * ex m x) x := by
  have h := hasDerivAt_fourier 1 m x
  simp only [Complex.ofReal_one, div_one] at h
  exact h

theorem ex_zero_pt (m : ℤ) : ex m 0 = 1 := by
  show fourier m ((0 : ℝ) : PhysicalCircle) = 1
  rw [fourier_coe_apply]
  simp

theorem ex_one_pt (m : ℤ) : ex m 1 = 1 := by
  have h : ((1 : ℝ) : PhysicalCircle) = ((0 : ℝ) : PhysicalCircle) := by
    rw [AddCircle.coe_period, QuotientAddGroup.mk_zero]
  simp only [ex]
  rw [h]
  simp

/-- `∫₀¹ e^{-2πimx} f(x) dx`. -/
def cf (f : ℝ → ℂ) (m : ℤ) : ℂ := ∫ x in (0 : ℝ)..1, ex (-m) x * f x

theorem cf_deriv {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hper : f 1 = f 0) (m : ℤ) : cf f' m = 2 * Real.pi * Complex.I * m * cf f m := by
  unfold cf
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (fun x _ => hasDerivAt_ex (-m) x) (fun x _ => hf x)
    ((continuous_const.mul (continuous_ex (-m))).intervalIntegrable 0 1)
    (hf'.intervalIntegrable 0 1)
  rw [h, ex_one_pt, ex_zero_pt, hper, sub_self, zero_sub]
  have h2 : (∫ x in (0 : ℝ)..1, 2 * Real.pi * Complex.I * ((-m : ℤ) : ℂ) * ex (-m) x * f x) =
      (2 * Real.pi * Complex.I * ((-m : ℤ) : ℂ)) * ∫ x in (0 : ℝ)..1, ex (-m) x * f x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [h2]
  push_cast
  ring

theorem norm_cf_le {f : ℝ → ℂ} {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (m : ℤ) : ‖cf f m‖ ≤ B := by
  unfold cf
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun x => ex (-m) x * f x) (C := B) (fun x _ => by rw [norm_mul, norm_ex, one_mul]; exact hB x)
  simpa using h

theorem cf_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (m : ℤ) :
    cf (fun x => f x - g x) m = cf f m - cf g m := by
  unfold cf
  rw [← intervalIntegral.integral_sub (f := fun x => ex (-m) x * f x)
    (g := fun x => ex (-m) x * g x) (((continuous_ex _).mul hf).intervalIntegrable 0 1)
    (((continuous_ex _).mul hg).intervalIntegrable 0 1)]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only
  ring

/-- Fourier coefficients of the time slices of a test function. -/
def cT (φ : ℝ × ℝ → ℂ) (m : ℤ) (t : ℝ) : ℂ := cf (fun x => φ (t, x)) m

theorem cT_Dx {φ : ℝ × ℝ → ℂ} (hφ : IsSpacetimeTest φ) (m : ℤ) (t : ℝ) :
    cT (Dx φ) m t = 2 * Real.pi * Complex.I * m * cT φ m t := by
  unfold cT
  refine cf_deriv (fun x => hasDerivAt_Dx hφ.smooth t x) ?_ ?_ m
  · exact hφ.dx.continuous.comp (continuous_const.prodMk continuous_id)
  · simpa using hφ.periodic t 0

theorem cT_DxDx {φ : ℝ × ℝ → ℂ} (hφ : IsSpacetimeTest φ) (m : ℤ) (t : ℝ) :
    cT (Dx (Dx φ)) m t = -((disp m : ℝ) : ℂ) * cT φ m t := by
  rw [cT_Dx hφ.dx, cT_Dx hφ, disp]
  push_cast
  rw [← mul_assoc, show (2 * (Real.pi : ℂ) * Complex.I * m * (2 * Real.pi * Complex.I * m)) =
    -((2 * Real.pi * m) ^ 2) * (Complex.I * Complex.I) * (-1) by ring, Complex.I_mul_I]
  ring

theorem disp_nonneg' (m : ℤ) : 0 ≤ disp m := by
  unfold disp; positivity

theorem cT_bound {φ : ℝ × ℝ → ℂ} (hφ : IsSpacetimeTest φ) :
    ∃ K, 0 ≤ K ∧ ∀ m t, ‖cT φ m t‖ ≤ K / (1 + disp m) := by
  have hψ := hφ.sub_smul hφ.dx.dx 1
  obtain ⟨K, hK0, hK⟩ := hψ.bounded
  refine ⟨K, hK0, fun m t => ?_⟩
  have hpos : 0 < 1 + disp m := by linarith [disp_nonneg' m]
  rw [le_div_iff₀ hpos]
  have h1 : cT (fun p => φ p - 1 * Dx (Dx φ) p) m t = (1 + disp m) * cT φ m t := by
    unfold cT
    have := cf_sub (f := fun x => φ (t, x)) (g := fun x => 1 * Dx (Dx φ) (t, x))
      (hφ.continuous.comp (continuous_const.prodMk continuous_id))
      (continuous_const.mul (hφ.dx.dx.continuous.comp (continuous_const.prodMk continuous_id))) m
    rw [this]
    have h2 := cT_DxDx hφ m t
    unfold cT at h2
    simp only [one_mul]
    rw [h2]
    ring
  have h3 := norm_cf_le (f := fun x => φ (t, x) - 1 * Dx (Dx φ) (t, x)) (fun x => hK (t, x)) m
  change ‖cT (fun p => φ p - 1 * Dx (Dx φ) p) m t‖ ≤ K at h3
  have hn : ‖(1 : ℂ) + ((disp m : ℝ) : ℂ)‖ = 1 + disp m := by
    rw [show (1 : ℂ) + ((disp m : ℝ) : ℂ) = ((1 + disp m : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg hpos.le]
  rw [h1, norm_mul, hn] at h3
  linarith

theorem summable_weight : Summable (fun m : ℤ => 1 / (1 + disp m)) := by
  have hg : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) := Real.summable_one_div_int_pow.2 (by norm_num)
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with m hm
  have hm2 : 0 < (m : ℝ) ^ 2 := by positivity
  have hpos : 0 < 1 + disp m := by linarith [disp_nonneg' m]
  rw [Real.norm_of_nonneg (by positivity)]
  refine one_div_le_one_div_of_le hm2 ?_
  have : (m : ℝ) ^ 2 ≤ disp m := by
    unfold disp
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have : (2 * Real.pi * m) ^ 2 = (2 * Real.pi) ^ 2 * (m : ℝ) ^ 2 := by ring
    rw [this]
    have h4 : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith
    nlinarith
  linarith

theorem summable_cT {φ : ℝ × ℝ → ℂ} (hφ : IsSpacetimeTest φ) (t : ℝ) :
    Summable (fun m => cT φ m t) := by
  obtain ⟨K, _, hK⟩ := cT_bound hφ
  refine Summable.of_norm_bounded (summable_weight.mul_left K) fun m => ?_
  rw [mul_one_div]
  exact hK m t

theorem coe_eq_fract (x : ℝ) : (x : PhysicalCircle) = ((Int.fract x : ℝ) : PhysicalCircle) := by
  refine (QuotientAddGroup.eq_iff_sub_mem).2 ?_
  rw [Int.self_sub_fract]
  exact AddSubgroup.mem_zmultiples_iff.2 ⟨⌊x⌋, by simp⟩

theorem cT_hasSum {φ : ℝ × ℝ → ℂ} (hφ : IsSpacetimeTest φ) (t x : ℝ) :
    HasSum (fun m => cT φ m t * ex m x) (φ (t, x)) := by
  set f : ℝ → ℂ := fun y => φ (t, y) with hfdef
  have hfc : Continuous f := hφ.continuous.comp (continuous_const.prodMk continuous_id)
  have hcont : Continuous (AddCircle.liftIco 1 0 f) :=
    AddCircle.liftIco_continuous (by simpa [f] using (hφ.periodic t 0).symm) hfc.continuousOn
  set G : C(PhysicalCircle, ℂ) := ⟨AddCircle.liftIco 1 0 f, hcont⟩
  have hcoef : ∀ m, fourierCoeff G m = cT φ m t := by
    intro m
    change fourierCoeff (AddCircle.liftIco 1 0 f) m = _
    rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
    simp only [cT, cf, ex, fourier_coe_apply, smul_eq_mul, zero_add, sub_zero, div_one,
      Complex.ofReal_one, one_smul]
    rfl
  have hsum : Summable (fourierCoeff G) := by
    have := summable_cT hφ t
    exact this.congr fun m => (hcoef m).symm
  have h := has_pointwise_sum_fourier_series_of_summable hsum (x : PhysicalCircle)
  have hG : G (x : PhysicalCircle) = φ (t, x) := by
    change AddCircle.liftIco 1 0 f (x : PhysicalCircle) = _
    rw [coe_eq_fract x, AddCircle.liftIco_coe_apply ⟨Int.fract_nonneg x, by
      rw [zero_add]; exact Int.fract_lt_one x⟩, hφ.eq_fract t x]
  rw [hG] at h
  convert h using 1
  funext m
  rw [hcoef m, smul_eq_mul]
  rfl

theorem cT_hasDerivAt {φ : ℝ × ℝ → ℂ} (hφ : IsSpacetimeTest φ) (m : ℤ) (t : ℝ) :
    HasDerivAt (fun s => cT φ m s) (cT (Dt φ) m t) t := by
  obtain ⟨B, _, hB⟩ := hφ.dt.bounded
  have hc : ∀ s, Continuous (fun x => ex (-m) x * φ (s, x)) := fun s =>
    (continuous_ex _).mul (hφ.continuous.comp (continuous_const.prodMk continuous_id))
  have hc' : Continuous (fun x => ex (-m) x * Dt φ (t, x)) :=
    (continuous_ex _).mul (hφ.dt.continuous.comp (continuous_const.prodMk continuous_id))
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (μ := volume) (a := 0) (b := 1) (bound := fun _ => B)
    (F := fun s x => ex (-m) x * φ (s, x)) (F' := fun s x => ex (-m) x * Dt φ (s, x))
    (x₀ := t) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => (hc s).aestronglyMeasurable)
    ((hc t).intervalIntegrable 0 1) hc'.aestronglyMeasurable
    (ae_of_all _ fun x _ s _ => by rw [norm_mul, norm_ex, one_mul]; exact hB _)
    intervalIntegrable_const
    (ae_of_all _ fun x _ s _ => (hasDerivAt_Dt hφ.smooth s x).const_mul (ex (-m) x))
  exact h.2

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
