import NlsGge.Spectral.ActualQuasimomentumContinuityE02_38
import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.Spectral.ActualGapHeightSemicircleE02_38
import NlsGge.Schur.ActualSchurE02Identification38V1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology Interval
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # E03-cont C3: continuity of the weighted gap integrals (v2 A:eq:gapcontinuous, campaign 38)

For fixed `n` and continuous `W`, `w ↦ (2/π)∫_{g_n(u_w)} W(2λ) v_{u_w}(λ) dλ` is continuous on H¹.
Route: two band points `x₁ < λ⁻_n(u₀)`, `x₂ > λ⁺_n(u₀)` with `Δh_{u₀}(xᵢ)² ≠ 1` keep their labels
`p_u(x₁) ∈ ((n-1)π, nπ)`, `p_u(x₂) ∈ (nπ, (n+1)π)` for `u` near `u₀` (C2); then the gap integral equals
the integral over the fixed window `[x₁, x₂]` (v vanishes off `g_n` there), which converges since
`v_u → v_{u₀}` uniformly on `[x₁, x₂]` (C1 plus uniform continuity of `s ↦ arcosh(max 1 s)`). -/

/-- Where `v ≠ 0`, the boundary real part `p` is an integer multiple of `π`. -/
theorem realPart_int_mul_pi_of_gapHeight_ne_zero_E02_38 (u : PhysicalL2) (x : ℝ)
    (hv : actualGapHeightE02_38 u x ≠ 0) :
    ∃ m : ℤ, actualQuasimomentumRealPartE02_38 u x = m * Real.pi := by
  set K := actualQuasimomentumBoundaryE02_38 u x
  have hq : K.im = actualGapHeightE02_38 u x :=
    boundaryLimit_im_E02_38 u x K (tendsto_actualQuasimomentumBoundaryE02_38 u x)
  have hqpos : 0 < K.im := by
    rw [hq]; exact lt_of_le_of_ne (actualGapHeightE02_38_nonneg u x) (Ne.symm hv)
  have hcos := actualQuasimomentumBoundaryE02_38_cos u x
  have hreal := actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 u x
  have him : (Complex.cos K).im = -(Real.sin K.re * Real.sinh K.im) := by
    conv_lhs => rw [← Complex.re_add_im K]
    rw [Complex.cos_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
      ← Complex.ofReal_sinh]
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.mul_re]
    ring
  rw [hcos, hreal] at him
  have hsh : Real.sinh K.im ≠ 0 := (Real.sinh_pos_iff.mpr hqpos).ne'
  have hsin : Real.sin K.re = 0 := by
    have : Real.sin K.re * Real.sinh K.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hsh
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsin
  exact ⟨m, hm.symm⟩

/-- The gap height vanishes at both labelled endpoints. -/
theorem gapHeight_endpoint_zero_E02_38 (u : PhysicalL2) (n : ℤ) :
    actualGapHeightE02_38 u (actualGapLowerAllE02_38 u n) = 0 ∧
    actualGapHeightE02_38 u (actualGapUpperAllE02_38 u n) = 0 := by
  obtain ⟨h1, h2⟩ := actualGapEndpoint_halfTrace_all_E02_38 u n
  have hc : ‖((Real.cos ((n:ℝ)*Real.pi) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  exact ⟨(actualGapHeightE02_38_eq_zero_iff u _).mpr (by rw [h1]; exact hc),
    (actualGapHeightE02_38_eq_zero_iff u _).mpr (by rw [h2]; exact hc)⟩

/-- Window identity: if the labels at `x₁, x₂` are in the adjacent open sectors, the `n`-th gap
integral equals the integral over `[x₁, x₂]`. -/
theorem gapIntegral_eq_window_E02_38 (u : PhysicalL2) (n : ℤ) (W : ℝ → ℝ) (hW : Continuous W)
    (x₁ x₂ : ℝ)
    (h1 : ((n:ℝ) - 1) * Real.pi < actualQuasimomentumRealPartE02_38 u x₁)
    (h1' : actualQuasimomentumRealPartE02_38 u x₁ < (n:ℝ) * Real.pi)
    (h2 : (n:ℝ) * Real.pi < actualQuasimomentumRealPartE02_38 u x₂)
    (h2' : actualQuasimomentumRealPartE02_38 u x₂ < ((n:ℝ) + 1) * Real.pi) :
    (∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        W (2 * x) * actualGapHeightE02_38 u x) =
      ∫ x in x₁..x₂, W (2 * x) * actualGapHeightE02_38 u x := by
  set a := actualGapLowerAllE02_38 u n
  set b := actualGapUpperAllE02_38 u n
  set p := actualQuasimomentumRealPartE02_38 u
  have hmono := monotone_actualQuasimomentumRealPartE02_38 u
  obtain ⟨hne, hset⟩ := actualGapLevelSet_eq_Icc_E02_38 u n
  have hab : a ≤ b := by
    obtain ⟨y, hy⟩ := hne; rw [hset] at hy; exact le_trans hy.1 hy.2
  have hpa : p a = (n:ℝ) * Real.pi := by
    have : a ∈ actualGapLevelSetE02_38 u n := by rw [hset]; exact ⟨le_rfl, hab⟩
    exact this
  have hpb : p b = (n:ℝ) * Real.pi := by
    have : b ∈ actualGapLevelSetE02_38 u n := by rw [hset]; exact ⟨hab, le_rfl⟩
    exact this
  have hx₁a : x₁ < a := by
    by_contra h; push Not at h
    have := hmono h; linarith
  have hbx₂ : b < x₂ := by
    by_contra h; push Not at h
    have := hmono h; linarith
  have hpi := Real.pi_pos
  -- v vanishes on [x₁, x₂] off the level set
  have hzero : ∀ x, x₁ ≤ x → x ≤ x₂ → p x ≠ (n:ℝ) * Real.pi → actualGapHeightE02_38 u x = 0 := by
    intro x hx1 hx2 hpx
    by_contra hv
    obtain ⟨m, hm⟩ := realPart_int_mul_pi_of_gapHeight_ne_zero_E02_38 u x hv
    have l1 := hmono hx1
    have l2 := hmono hx2
    simp only [p] at hpx l1 l2
    rw [hm] at hpx l1 l2
    have r1 : ((n:ℝ) - 1) < m := by nlinarith
    have r2 : (m:ℝ) < (n:ℝ) + 1 := by nlinarith
    have r1' : n - 1 < m := by exact_mod_cast r1
    have r2' : m < n + 1 := by exact_mod_cast r2
    have : m = n := by omega
    exact hpx (by rw [this])
  have hint : ∀ c d : ℝ, IntervalIntegrable (fun x => W (2 * x) * actualGapHeightE02_38 u x)
      MeasureTheory.volume c d := fun c d =>
    ((hW.comp (continuous_const.mul continuous_id)).mul
      (continuous_actualGapHeightE02_38 u)).intervalIntegrable c d
  have hend := gapHeight_endpoint_zero_E02_38 u n
  have hL : (∫ x in x₁..a, W (2 * x) * actualGapHeightE02_38 u x) = 0 := by
    rw [← intervalIntegral.integral_zero (a := x₁) (b := a) (μ := MeasureTheory.volume)]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [uIcc_of_le hx₁a.le] at hx
    simp only
    rcases lt_or_eq_of_le hx.2 with hlt | heq
    · have : p x ≠ (n:ℝ) * Real.pi := by
        intro hpx
        have : x ∈ actualGapLevelSetE02_38 u n := hpx
        rw [hset] at this; linarith [this.1]
      rw [hzero x hx.1 (by linarith) this, mul_zero]
    · rw [heq, hend.1, mul_zero]
  have hR : (∫ x in b..x₂, W (2 * x) * actualGapHeightE02_38 u x) = 0 := by
    rw [← intervalIntegral.integral_zero (a := b) (b := x₂) (μ := MeasureTheory.volume)]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [uIcc_of_le hbx₂.le] at hx
    simp only
    rcases lt_or_eq_of_le hx.1 with hlt | heq
    · have : p x ≠ (n:ℝ) * Real.pi := by
        intro hpx
        have : x ∈ actualGapLevelSetE02_38 u n := hpx
        rw [hset] at this; linarith [this.2]
      rw [hzero x (by linarith) hx.2 this, mul_zero]
    · rw [← heq, hend.2, mul_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint x₁ a) (hint a x₂),
    ← intervalIntegral.integral_add_adjacent_intervals (hint a b) (hint b x₂), hL, hR]
  ring

/-- Existence of a left/right band point near a gap endpoint with a prescribed label window. -/
theorem exists_band_point_left_E02_38 (u : PhysicalL2) (a c : ℝ) (hc : c < actualQuasimomentumRealPartE02_38 u a) :
    ∃ x, x < a ∧ c < actualQuasimomentumRealPartE02_38 u x ∧
      actualPhysicalUnitHalfTrace32 u (x:ℂ) ^ 2 ≠ 1 := by
  have hcont := (continuous_actualQuasimomentumRealPartE02_38 u).continuousAt (x := a)
  have e1 : ∀ᶠ y in 𝓝[<] a, c < actualQuasimomentumRealPartE02_38 u y :=
    nhdsWithin_le_nhds (hcont.eventually (lt_mem_nhds hc))
  have e2 : ∀ᶠ y : ℝ in 𝓝[<] a, actualPhysicalUnitHalfTrace32 u (y:ℂ) ^ 2 ≠ 1 :=
    nhdsWithin_mono _ (fun y (hy : y < a) => ne_of_lt hy) (halfTrace_sq_ne_one_eventually_E02_38 u a)
  have e3 : ∀ᶠ y in 𝓝[<] a, y < a := self_mem_nhdsWithin
  obtain ⟨x, hx3, hx1, hx2⟩ := (e3.and (e1.and e2)).exists
  exact ⟨x, hx3, hx1, hx2⟩

theorem exists_band_point_right_E02_38 (u : PhysicalL2) (b c : ℝ) (hc : actualQuasimomentumRealPartE02_38 u b < c) :
    ∃ x, b < x ∧ actualQuasimomentumRealPartE02_38 u x < c ∧
      actualPhysicalUnitHalfTrace32 u (x:ℂ) ^ 2 ≠ 1 := by
  have hcont := (continuous_actualQuasimomentumRealPartE02_38 u).continuousAt (x := b)
  have e1 : ∀ᶠ y in 𝓝[>] b, actualQuasimomentumRealPartE02_38 u y < c :=
    nhdsWithin_le_nhds (hcont.eventually (gt_mem_nhds hc))
  have e2 : ∀ᶠ y : ℝ in 𝓝[>] b, actualPhysicalUnitHalfTrace32 u (y:ℂ) ^ 2 ≠ 1 :=
    nhdsWithin_mono _ (fun y (hy : b < y) => ne_of_gt hy) (halfTrace_sq_ne_one_eventually_E02_38 u b)
  have e3 : ∀ᶠ y in 𝓝[>] b, b < y := self_mem_nhdsWithin
  obtain ⟨x, hx3, hx1, hx2⟩ := (e3.and (e1.and e2)).exists
  exact ⟨x, hx3, hx1, hx2⟩

/-- Uniform closeness of the gap heights on a compact window, for `u` L²-close to `u₀`. -/
theorem gapHeight_uniform_close_E02_38 (u₀ : PhysicalL2) (x₁ x₂ : ℝ) :
    ∀ ε' : ℝ, 0 < ε' → ∃ τ : ℝ, 0 < τ ∧ ∀ u : PhysicalL2, ‖u - u₀‖ ≤ τ →
      ∀ x ∈ Icc x₁ x₂, |actualGapHeightE02_38 u x - actualGapHeightE02_38 u₀ x| < ε' := by
  intro ε' hε'
  set Z := |x₁| + |x₂|
  have hZ : ∀ x ∈ Icc x₁ x₂, ‖(x:ℂ)‖ ≤ Z := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs]
    simp only [Z]
    rcases le_total 0 x with h0 | h0
    · rw [abs_of_nonneg h0]; linarith [le_abs_self x₂, hx.2, abs_nonneg x₁]
    · rw [abs_of_nonpos h0]; linarith [hx.1, abs_nonneg x₂, neg_le_abs x₁]
  obtain ⟨CL, hCL, hLip⟩ := actualPhysicalUnitHalfTrace_lipschitz_E02_38 (‖u₀‖ + 1) Z
    (by positivity) (by positivity)
  have hΔc : Continuous (fun x : ℝ => actualPhysicalUnitHalfTrace32 u₀ (x:ℂ)) :=
    ((analyticOnNhd_actualPhysicalUnitHalfTrace32 u₀).continuousOn.comp_continuous
      Complex.continuous_ofReal (fun _ => Set.mem_univ _))
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := x₁) (b := x₂)).exists_bound_of_continuousOn
    hΔc.continuousOn
  set S := |M₀| + CL + 1
  have hF : Continuous (fun s : ℝ => Real.arcosh (max 1 s)) :=
    Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
      (fun _ => Set.mem_Ici.mpr (le_max_left _ _))
  have hFu := (isCompact_Icc (a := (0:ℝ)) (b := S)).uniformContinuousOn_of_continuous
    hF.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hFu
  obtain ⟨δF, hδF, hFδ⟩ := hFu ε' hε'
  refine ⟨min 1 (δF / (2 * (CL + 1))), lt_min one_pos (by positivity), ?_⟩
  intro u hdu x hx
  have hτ1 : ‖u - u₀‖ ≤ 1 := le_trans hdu (min_le_left _ _)
  have hτF : ‖u - u₀‖ ≤ δF / (2 * (CL + 1)) := le_trans hdu (min_le_right _ _)
  have hun : ‖u‖ ≤ ‖u₀‖ + 1 := by
    have h := norm_add_le u₀ (u - u₀); rw [add_sub_cancel] at h; linarith
  have hL := hLip u u₀ hun (by linarith) (x:ℂ) (hZ x hx)
  set A := actualPhysicalUnitHalfTrace32 u (x:ℂ)
  set A₀ := actualPhysicalUnitHalfTrace32 u₀ (x:ℂ)
  have hs₀ : ‖A₀‖ ≤ |M₀| := le_trans (hM₀ x hx) (le_abs_self _)
  have hd1 : CL * ‖u - u₀‖ ≤ CL := by nlinarith [norm_nonneg (u - u₀)]
  have hd2 : CL * ‖u - u₀‖ ≤ CL * (δF / (2 * (CL + 1))) := mul_le_mul_of_nonneg_left hτF hCL
  have hd3 : CL * (δF / (2 * (CL + 1))) < δF := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have h1 := abs_norm_sub_norm_le A A₀
  have hs : ‖A‖ ≤ S := by
    have := norm_sub_norm_le A A₀
    simp only [S]; linarith
  have hdist : dist ‖A‖ ‖A₀‖ < δF := by rw [Real.dist_eq]; linarith
  have := hFδ _ ⟨norm_nonneg _, hs⟩ _ ⟨norm_nonneg _, by simp only [S]; linarith⟩ hdist
  rw [Real.dist_eq] at this
  exact this

/-- Weighted window integrals are close when the integrands are uniformly close. -/
theorem window_integral_close_E02_38 (W : ℝ → ℝ) (hW : Continuous W) (x₁ x₂ : ℝ) (h : x₁ < x₂) :
    ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧ ∀ v v₀ : ℝ → ℝ, Continuous v → Continuous v₀ →
      (∀ x ∈ Icc x₁ x₂, |v x - v₀ x| < ε') →
      |(2 / Real.pi) * (∫ x in x₁..x₂, W (2 * x) * v x) -
        (2 / Real.pi) * (∫ x in x₁..x₂, W (2 * x) * v₀ x)| < ε := by
  intro ε hε
  have hW2 : Continuous (fun x : ℝ => W (2 * x)) := hW.comp (continuous_const.mul continuous_id)
  obtain ⟨MW, hMW⟩ := (isCompact_Icc (a := x₁) (b := x₂)).exists_bound_of_continuousOn
    hW2.continuousOn
  have hden : 0 < 4 * (|MW| + 1) * (x₂ - x₁ + 1) := by
    have : 0 < x₂ - x₁ + 1 := by linarith
    positivity
  refine ⟨ε / (4 * (|MW| + 1) * (x₂ - x₁ + 1)), div_pos hε hden, ?_⟩
  intro v v₀ hv hv₀ hclose
  set ε' := ε / (4 * (|MW| + 1) * (x₂ - x₁ + 1))
  have hint : ∀ f : ℝ → ℝ, Continuous f →
      IntervalIntegrable (fun x => W (2 * x) * f x) MeasureTheory.volume x₁ x₂ :=
    fun f hf => (hW2.mul hf).intervalIntegrable _ _
  rw [← mul_sub, ← intervalIntegral.integral_sub (hint v hv) (hint v₀ hv₀)]
  have hbound : ∀ x ∈ Ι x₁ x₂, ‖W (2 * x) * v x - W (2 * x) * v₀ x‖ ≤ |MW| * ε' := by
    intro x hx
    rw [uIoc_of_le h.le] at hx
    have hxI : x ∈ Icc x₁ x₂ := ⟨hx.1.le, hx.2⟩
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (le_trans (hMW x hxI) (le_abs_self _)) (hclose x hxI).le (abs_nonneg _)
      (abs_nonneg _)
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [abs_of_pos (sub_pos.mpr h)] at hI
  have hkey : |MW| * ε' * (x₂ - x₁) ≤ ε / 4 := by
    have e : |MW| * ε' * (x₂ - x₁) = ε * (|MW| * (x₂ - x₁)) / (4 * (|MW| + 1) * (x₂ - x₁ + 1)) := by
      simp only [ε']; field_simp
    rw [e, div_le_iff₀ hden]
    have : |MW| * (x₂ - x₁) ≤ (|MW| + 1) * (x₂ - x₁ + 1) := by
      nlinarith [abs_nonneg MW]
    nlinarith
  have hn := le_trans hI hkey
  rw [Real.norm_eq_abs] at hn
  have hpi := Real.pi_pos
  have h2pi : 2 / Real.pi < 1 := by rw [div_lt_one hpi]; linarith [Real.pi_gt_three]
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / Real.pi)]
  have : 2 / Real.pi * |∫ x in x₁..x₂, (W (2 * x) * v x - W (2 * x) * v₀ x)| ≤ 1 * (ε / 4) :=
    mul_le_mul h2pi.le hn (abs_nonneg _) zero_le_one
  linarith

/-- Label stability from the Hölder bound of C2. -/
theorem re_lt_of_holder_E02_38 (C μ t : ℝ) (hC : 0 ≤ C) (hμ : 0 < μ) (ht : 0 ≤ t)
    (htμ : t ≤ μ^2 / (37 * (C + 1))) (d : ℂ) (hd : ‖d‖ ≤ 6 * Real.sqrt (C * t)) : |d.re| < μ := by
  have h2 : C * t ≤ μ^2 / 37 := by
    have e1 : C * t ≤ (C + 1) * t := by nlinarith
    have e2 : (C + 1) * t ≤ (C + 1) * (μ^2 / (37 * (C + 1))) :=
      mul_le_mul_of_nonneg_left htμ (by linarith)
    have e3 : (C + 1) * (μ^2 / (37 * (C + 1))) = μ^2 / 37 := by field_simp
    linarith
  have h3 : Real.sqrt (C * t) < μ / 6 := by
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith
  have := Complex.abs_re_le_norm d
  linarith

/-- **E03-cont (v2 A:eq:gapcontinuous).** For fixed `n ∈ ℤ` and continuous `W`, the weighted gap
integral `(2/π)∫_{g_n(u)} W(2λ) v_u(λ) dλ` is continuous on H¹ (`u = u_w` the Schur H¹ carrier). -/
theorem actualGapAction_continuous_E02_38 (n : ℤ) (W : ℝ → ℝ) (hW : Continuous W) :
    Continuous (fun w : WeightedHilbert (sobolevModeWeight (1:ℝ)) =>
      (2 / Real.pi) * ∫ x in (actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n)..
        (actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n),
        W (2 * x) * actualGapHeightE02_38 (physicalH1ComplexCarrierToL2Actual22 w) x) := by
  rw [continuous_iff_continuousAt]
  intro w₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨c, hc⟩ : ∃ c, c = physicalH1ComplexCarrierToL2Actual22 := ⟨_, rfl⟩
  rw [← hc]
  obtain ⟨u₀, hu₀d⟩ : ∃ u₀, u₀ = c w₀ := ⟨_, rfl⟩
  have hu₀ : SobolevSquareSummable 1 (physicalFourier u₀) := by
    rw [hu₀d, hc]; exact physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w₀
  have hnormc : ∀ w (hw : SobolevSquareSummable 1 (physicalFourier (c w))),
      ‖physicalSobolevL2 1 (c w) hw‖ = ‖w‖ := by
    intro w hw; subst hc; exact physicalSobolevL2_norm_h1Carrier38 w
  have hsumc : ∀ w, SobolevSquareSummable 1 (physicalFourier (c w)) := by
    intro w; subst hc; exact physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w
  set B := ‖w₀‖ + 1
  have hB : 1 ≤ B := by simp only [B]; linarith [norm_nonneg w₀]
  have hu₀B : ‖physicalSobolevL2 1 u₀ hu₀‖ ≤ B := by
    subst hu₀d; rw [hnormc]; simp only [B]; linarith
  rw [← hu₀d]
  have hmono := monotone_actualQuasimomentumRealPartE02_38 u₀
  obtain ⟨hne, hset⟩ := actualGapLevelSet_eq_Icc_E02_38 u₀ n
  obtain ⟨a, ha⟩ : ∃ a, a = actualGapLowerAllE02_38 u₀ n := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = actualGapUpperAllE02_38 u₀ n := ⟨_, rfl⟩
  rw [← ha, ← hb] at hset
  have hab : a ≤ b := by
    obtain ⟨y, hy⟩ := hne; rw [hset] at hy; exact le_trans hy.1 hy.2
  have hpa : actualQuasimomentumRealPartE02_38 u₀ a = (n:ℝ) * Real.pi := by
    have : a ∈ actualGapLevelSetE02_38 u₀ n := by rw [hset]; exact ⟨le_rfl, hab⟩
    exact this
  have hpb : actualQuasimomentumRealPartE02_38 u₀ b = (n:ℝ) * Real.pi := by
    have : b ∈ actualGapLevelSetE02_38 u₀ n := by rw [hset]; exact ⟨hab, le_rfl⟩
    exact this
  have hpi := Real.pi_pos
  obtain ⟨x₁, hx₁a, hx₁p, hx₁Δ⟩ :=
    exists_band_point_left_E02_38 u₀ a (((n:ℝ) - 1) * Real.pi) (by rw [hpa]; nlinarith)
  obtain ⟨x₂, hbx₂, hx₂p, hx₂Δ⟩ :=
    exists_band_point_right_E02_38 u₀ b (((n:ℝ) + 1) * Real.pi) (by rw [hpb]; nlinarith)
  have hp₁ : actualQuasimomentumRealPartE02_38 u₀ x₁ < (n:ℝ) * Real.pi := by
    refine lt_of_le_of_ne (hpa ▸ hmono hx₁a.le) ?_
    intro h
    have : x₁ ∈ actualGapLevelSetE02_38 u₀ n := h
    rw [hset] at this; linarith [this.1]
  have hp₂ : (n:ℝ) * Real.pi < actualQuasimomentumRealPartE02_38 u₀ x₂ := by
    refine lt_of_le_of_ne (hpb ▸ hmono hbx₂.le) ?_
    intro h
    have : x₂ ∈ actualGapLevelSetE02_38 u₀ n := h.symm
    rw [hset] at this; linarith [this.2]
  have hx₁₂ : x₁ < x₂ := by linarith
  obtain ⟨μ, hμ, hμ1, hμ2, hμ3, hμ4⟩ : ∃ μ : ℝ, 0 < μ ∧
      μ ≤ actualQuasimomentumRealPartE02_38 u₀ x₁ - ((n:ℝ) - 1) * Real.pi ∧
      μ ≤ (n:ℝ) * Real.pi - actualQuasimomentumRealPartE02_38 u₀ x₁ ∧
      μ ≤ actualQuasimomentumRealPartE02_38 u₀ x₂ - (n:ℝ) * Real.pi ∧
      μ ≤ ((n:ℝ) + 1) * Real.pi - actualQuasimomentumRealPartE02_38 u₀ x₂ :=
    ⟨_, lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith)),
      le_trans (min_le_left _ _) (min_le_left _ _), le_trans (min_le_left _ _) (min_le_right _ _),
      le_trans (min_le_right _ _) (min_le_left _ _), le_trans (min_le_right _ _) (min_le_right _ _)⟩
  obtain ⟨C₁, hC₁, δ₁, hδ₁, hk₁⟩ :=
    actualQuasimomentumBoundary_holder_in_u_E02_38 u₀ hu₀ B hB hu₀B x₁ hx₁Δ
  obtain ⟨C₂, hC₂, δ₂, hδ₂, hk₂⟩ :=
    actualQuasimomentumBoundary_holder_in_u_E02_38 u₀ hu₀ B hB hu₀B x₂ hx₂Δ
  obtain ⟨ε', hε', hwin⟩ := window_integral_close_E02_38 W hW x₁ x₂ hx₁₂ ε hε
  obtain ⟨τv, hτv, hvclose⟩ := gapHeight_uniform_close_E02_38 u₀ x₁ x₂ ε' hε'
  obtain ⟨τ, hτ, hτ1, hτδ₁, hτδ₂, hτv', hτμ₁, hτμ₂⟩ : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ τ ≤ δ₁ ∧ τ ≤ δ₂ ∧
      τ ≤ τv ∧ τ ≤ μ^2 / (37 * (C₁ + 1)) ∧ τ ≤ μ^2 / (37 * (C₂ + 1)) :=
    ⟨min (min (min 1 δ₁) (min δ₂ τv)) (min (μ^2 / (37 * (C₁ + 1))) (μ^2 / (37 * (C₂ + 1)))),
      lt_min (lt_min (lt_min one_pos hδ₁) (lt_min hδ₂ hτv)) (lt_min (by positivity) (by positivity)),
      le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)),
      le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)),
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)),
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)),
      le_trans (min_le_right _ _) (min_le_left _ _), le_trans (min_le_right _ _) (min_le_right _ _)⟩
  have hc0 := norm_nonneg c
  refine ⟨τ / (‖c‖ + 1), by positivity, ?_⟩
  intro w hw
  obtain ⟨u, hud⟩ : ∃ u, u = c w := ⟨_, rfl⟩
  rw [← hud]
  have hu : SobolevSquareSummable 1 (physicalFourier u) := hud ▸ hsumc w
  have hwd : ‖w - w₀‖ ≤ τ / (‖c‖ + 1) := by rw [← dist_eq_norm]; exact hw.le
  have hτc : τ / (‖c‖ + 1) ≤ τ := div_le_self hτ.le (by linarith)
  have hdu : ‖u - u₀‖ ≤ τ := by
    have : u - u₀ = c (w - w₀) := by rw [hud, hu₀d, map_sub]
    rw [this]
    calc ‖c (w - w₀)‖ ≤ ‖c‖ * ‖w - w₀‖ := c.le_opNorm _
      _ ≤ ‖c‖ * (τ / (‖c‖ + 1)) := mul_le_mul_of_nonneg_left hwd hc0
      _ ≤ τ := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have huB : ‖physicalSobolevL2 1 u hu‖ ≤ B := by
    have e : ‖physicalSobolevL2 1 u hu‖ = ‖w‖ := by subst hud; exact hnormc w hu
    rw [e]
    have h2 : ‖w‖ ≤ ‖w₀‖ + ‖w - w₀‖ := by
      have h := norm_add_le w₀ (w - w₀); rwa [add_sub_cancel] at h
    simp only [B]; linarith
  have hl₁ := re_lt_of_holder_E02_38 C₁ μ ‖u - u₀‖ hC₁ hμ (norm_nonneg _) (hdu.trans hτμ₁) _
    (hk₁ u hu huB (hdu.trans hτδ₁))
  have hl₂ := re_lt_of_holder_E02_38 C₂ μ ‖u - u₀‖ hC₂ hμ (norm_nonneg _) (hdu.trans hτμ₂) _
    (hk₂ u hu huB (hdu.trans hτδ₂))
  rw [Complex.sub_re] at hl₁ hl₂
  change |actualQuasimomentumRealPartE02_38 u x₁ - actualQuasimomentumRealPartE02_38 u₀ x₁| < μ at hl₁
  change |actualQuasimomentumRealPartE02_38 u x₂ - actualQuasimomentumRealPartE02_38 u₀ x₂| < μ at hl₂
  rw [abs_lt] at hl₁ hl₂
  rw [Real.dist_eq, gapIntegral_eq_window_E02_38 u n W hW x₁ x₂ (by linarith) (by linarith)
      (by linarith) (by linarith),
    gapIntegral_eq_window_E02_38 u₀ n W hW x₁ x₂ (by linarith) (by linarith) (by linarith)
      (by linarith)]
  exact hwin _ _ (continuous_actualGapHeightE02_38 u) (continuous_actualGapHeightE02_38 u₀)
    (hvclose u (hdu.trans hτv'))

end NlsGge.SpectralFoundations
end
