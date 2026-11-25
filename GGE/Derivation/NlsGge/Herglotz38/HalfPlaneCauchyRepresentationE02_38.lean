import Mathlib

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

open Complex MeasureTheory Filter Topology Set

lemma sqrt_cube_bound_E02_38 {B : ℝ} (hB : 0 ≤ B) {w : ℂ} {X : ℝ} (hX : 0 < X) (h : X ≤ ‖w‖) :
    B / (Real.sqrt (1 + ‖w‖)) ^ 3 ≤ B / (Real.sqrt (1 + X)) ^ 3 := by
  have h1 : 0 < Real.sqrt (1 + X) := Real.sqrt_pos.2 (by linarith)
  have h2 : Real.sqrt (1 + X) ≤ Real.sqrt (1 + ‖w‖) := Real.sqrt_le_sqrt (by linarith)
  exact div_le_div_of_nonneg_left hB (pow_pos h1 3) (pow_le_pow_left₀ h1.le h2 3)

lemma edge_bound_E02_38 {B : ℝ} (hB : 0 ≤ B) {X : ℝ} (hX : 0 < X) (k : ℝ) (_hk : 0 ≤ k) (hk4 : k ≤ 2) :
    k * X * (B / (Real.sqrt (1 + X)) ^ 3) ≤ 2 * B / Real.sqrt (1 + X) := by
  have h1 : 0 < Real.sqrt (1 + X) := Real.sqrt_pos.2 (by linarith)
  have h2 : (Real.sqrt (1 + X)) ^ 2 = 1 + X := Real.sq_sqrt (by linarith)
  have : k * X * (B / (Real.sqrt (1 + X)) ^ 3) = (k * X * B) / (Real.sqrt (1 + X)) ^ 3 := by ring
  rw [this, div_le_div_iff₀ (pow_pos h1 3) h1]
  have : (2 * B) * (Real.sqrt (1 + X)) ^ 3 = 2 * B * (1 + X) * Real.sqrt (1 + X) := by
    rw [pow_succ, h2]; ring
  rw [this]
  have h3 : k * X * B * Real.sqrt (1 + X) ≤ 2 * B * (1 + X) * Real.sqrt (1 + X) := by
    apply mul_le_mul_of_nonneg_right _ h1.le
    have : k * X ≤ 2 * (1 + X) := by nlinarith
    nlinarith
  exact h3

theorem cauchy_decay_E02_38 (G : ℂ → ℂ) (B : ℝ)
    (hd : DifferentiableOn ℂ G {z | 0 < z.im}) (hc : ContinuousOn G {z | 0 ≤ z.im})
    (hb : ∀ w : ℂ, 0 ≤ w.im → ‖G w‖ ≤ B / (Real.sqrt (1 + ‖w‖)) ^ 3) :
    Integrable (fun t : ℝ => G (t : ℂ)) ∧ ∫ t : ℝ, G (t : ℂ) = 0 := by
  have hB : 0 ≤ B := by
    have := hb 0 (by simp)
    simp at this
    exact le_trans (norm_nonneg _) this
  have hcont : Continuous (fun t : ℝ => G (t : ℂ)) := by
    refine continuousOn_univ.1 ?_
    exact hc.comp Complex.continuous_ofReal.continuousOn (fun t _ => by simp)
  have hint : Integrable (fun t : ℝ => G (t : ℂ)) := by
    have hi : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(3/2 : ℝ))) :=
      integrable_one_add_norm (by simp; norm_num)
    refine (hi.const_mul B).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    have h1 := hb (t : ℂ) (by simp)
    simp only [Complex.norm_real] at h1 ⊢
    refine h1.trans (le_of_eq ?_)
    have : (1 + ‖t‖) ≥ 0 := by positivity
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul this, Real.rpow_neg this]
    norm_num
    ring
  refine ⟨hint, ?_⟩
  -- rectangle identity
  have hrect : ∀ X : ℝ, 0 < X →
      (∫ x : ℝ in (-X)..X, G (x : ℂ)) =
        (∫ x : ℝ in (-X)..X, G (x + X * I)) - I • (∫ y : ℝ in (0:ℝ)..X, G (X + y * I)) +
          I • (∫ y : ℝ in (0:ℝ)..X, G (-X + y * I)) := by
    intro X hX
    have := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn G
      ((-X : ℝ) : ℂ) ⟨X, X⟩ ?_ ?_
    · simp at this
      linear_combination this
    · refine hc.mono ?_
      intro w hw
      simp only [mem_reProdIm] at hw
      have := hw.2
      simp [Set.uIcc_of_le hX.le] at this
      exact this.1
    · refine hd.mono ?_
      intro w hw
      simp only [mem_reProdIm] at hw
      have h0 : min ((((-X : ℝ) : ℂ)).im) X = 0 := by simp [hX.le]
      have := hw.2.1
      rw [h0] at this
      exact this
  -- edge decay
  have hz : ∀ (E : ℝ → ℂ) (k : ℝ), 0 ≤ k → k ≤ 2 →
      (∀ᶠ X in atTop, ‖E X‖ ≤ k * X * (B / (Real.sqrt (1 + X)) ^ 3)) →
      Tendsto E atTop (𝓝 0) := by
    intro E k hk0 hk2 hev
    have hs : Tendsto (fun X : ℝ => Real.sqrt (1 + X)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_left _ _ tendsto_id)
    have hlim : Tendsto (fun X : ℝ => 2 * B / Real.sqrt (1 + X)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hs
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev, eventually_gt_atTop 0] with X hX hX0
    exact hX.trans (edge_bound_E02_38 hB hX0 k hk0 hk2)
  have hI : Tendsto (fun X : ℝ => ∫ x : ℝ in (-X)..X, G (x : ℂ)) atTop (𝓝 (∫ t : ℝ, G (t : ℂ))) :=
    intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hTop : Tendsto (fun X : ℝ => ∫ x : ℝ in (-X)..X, G (x + X * I)) atTop (𝓝 0) := by
    refine hz _ 2 (by norm_num) le_rfl ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => G (x + X * I)) (a := -X) (b := X) (C := B / (Real.sqrt (1 + X)) ^ 3) ?_
    · have e : |X - -X| = 2 * X := by rw [abs_of_nonneg (by linarith)]; ring
      rw [e] at this
      linarith
    · intro x _
      have him : 0 ≤ (x + X * I : ℂ).im := by simp [hX.le]
      refine (hb _ him).trans (sqrt_cube_bound_E02_38 hB hX ?_)
      have := Complex.abs_im_le_norm (x + X * I : ℂ)
      simpa [abs_of_pos hX] using this
  have hRight : Tendsto (fun X : ℝ => I • ∫ y : ℝ in (0:ℝ)..X, G (X + y * I)) atTop (𝓝 0) := by
    refine hz _ 1 (by norm_num) (by norm_num) ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y : ℝ => G (X + y * I)) (a := 0) (b := X) (C := B / (Real.sqrt (1 + X)) ^ 3) ?_
    · have e : |X - 0| = X := by rw [sub_zero, abs_of_pos hX]
      rw [e] at this
      simpa [mul_comm] using this
    · intro y hy
      rw [Set.uIoc_of_le hX.le] at hy
      have him : 0 ≤ (X + y * I : ℂ).im := by simp [hy.1.le]
      refine (hb _ him).trans (sqrt_cube_bound_E02_38 hB hX ?_)
      have := Complex.abs_re_le_norm (X + y * I : ℂ)
      simpa [abs_of_pos hX] using this
  have hLeft : Tendsto (fun X : ℝ => I • ∫ y : ℝ in (0:ℝ)..X, G (-X + y * I)) atTop (𝓝 0) := by
    refine hz _ 1 (by norm_num) (by norm_num) ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y : ℝ => G (-X + y * I)) (a := 0) (b := X) (C := B / (Real.sqrt (1 + X)) ^ 3) ?_
    · have e : |X - 0| = X := by rw [sub_zero, abs_of_pos hX]
      rw [e] at this
      simpa [mul_comm] using this
    · intro y hy
      rw [Set.uIoc_of_le hX.le] at hy
      have him : 0 ≤ (-X + y * I : ℂ).im := by simp [hy.1.le]
      refine (hb _ him).trans (sqrt_cube_bound_E02_38 hB hX ?_)
      have := Complex.abs_re_le_norm (-X + y * I : ℂ)
      simpa [abs_of_pos hX] using this
  have h0 : Tendsto (fun X : ℝ => ∫ x : ℝ in (-X)..X, G (x : ℂ)) atTop (𝓝 0) := by
    have := (hTop.sub hRight).add hLeft
    simp only [sub_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    rw [hrect X hX]
  exact tendsto_nhds_unique hI h0


lemma poisson_kernel_E02_38 (x y : ℝ) (hy : 0 < y) :
    Integrable (fun t : ℝ => ((t - x) ^ 2 + y ^ 2)⁻¹) ∧
      ∫ t : ℝ, ((t - x) ^ 2 + y ^ 2)⁻¹ = Real.pi / y := by
  have hy0 : y ≠ 0 := hy.ne'
  have heq : (fun t : ℝ => ((t - x) ^ 2 + y ^ 2)⁻¹) =
      fun t : ℝ => (y ^ 2)⁻¹ * (fun s : ℝ => (fun u : ℝ => (1 + u ^ 2)⁻¹) (s / y)) (t - x) := by
    funext t
    have : (1 + ((t - x) / y) ^ 2) = ((t - x) ^ 2 + y ^ 2) / y ^ 2 := by
      field_simp
      ring
    simp only [this]
    have hpos : 0 < (t - x) ^ 2 + y ^ 2 := by positivity
    field_simp
  rw [heq]
  have hi : Integrable (fun s : ℝ => (fun u : ℝ => (1 + u ^ 2)⁻¹) (s / y)) :=
    integrable_inv_one_add_sq.comp_div hy0
  refine ⟨(hi.comp_sub_right x).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun s : ℝ => (fun u : ℝ => (1 + u ^ 2)⁻¹) (s / y)) x,
    Measure.integral_comp_div (fun u : ℝ => (1 + u ^ 2)⁻¹) y, integral_univ_inv_one_add_sq,
    abs_of_pos hy, smul_eq_mul]
  field_simp

/-- `1/‖w - a‖` decay when `a` lies strictly below the real axis and `w` in the closed upper
half-plane. -/
lemma inv_dist_bound_E02_38 (a : ℂ) (ha : a.im < 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ w : ℂ, 0 ≤ w.im → 1 + ‖w‖ ≤ K * ‖w - a‖ := by
  refine ⟨1 + (1 + ‖a‖) / (-a.im), by
    have : 0 ≤ (1 + ‖a‖) / (-a.im) := by
      apply div_nonneg (by positivity) (by linarith)
    linarith, fun w hw => ?_⟩
  have hδ : 0 < -a.im := by linarith
  have h1 : -a.im ≤ ‖w - a‖ := by
    have := Complex.abs_im_le_norm (w - a)
    have h2 : (w - a).im = w.im - a.im := by simp
    rw [h2] at this
    have : w.im - a.im ≤ |w.im - a.im| := le_abs_self _
    linarith [Complex.abs_im_le_norm (w - a), (show (w - a).im = w.im - a.im by simp)]
  have h2 : ‖w‖ ≤ ‖w - a‖ + ‖a‖ := by
    have := norm_le_insert' w a
    linarith [norm_sub_le_norm_add (w - a) a, sub_add_cancel w a]
  have h3 : (1 + ‖a‖) ≤ (1 + ‖a‖) / (-a.im) * ‖w - a‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith [norm_nonneg (w - a)]


lemma sqrt_sq_E02_38 (w : ℂ) : Real.sqrt (1 + ‖w‖) ^ 2 = 1 + ‖w‖ :=
  Real.sq_sqrt (by positivity)

lemma sqrt_ge_one_E02_38 (w : ℂ) : 1 ≤ Real.sqrt (1 + ‖w‖) := by
  exact Real.one_le_sqrt.2 (by linarith [norm_nonneg w])

/-- Eventual cube-root-type decay plus continuity on the closed upper half-plane gives a global
bound. -/
lemma global_bound_E02_38 (G : ℂ → ℂ) (hc : ContinuousOn G {z | 0 ≤ z.im}) (B R : ℝ)
    (hb : ∀ w : ℂ, 0 ≤ w.im → R ≤ ‖w‖ → ‖G w‖ ≤ B / (Real.sqrt (1 + ‖w‖)) ^ 3) :
    ∃ B' : ℝ, ∀ w : ℂ, 0 ≤ w.im → ‖G w‖ ≤ B' / (Real.sqrt (1 + ‖w‖)) ^ 3 := by
  have hK : IsCompact ({z : ℂ | 0 ≤ z.im} ∩ Metric.closedBall (0 : ℂ) R) :=
    (isCompact_closedBall (0 : ℂ) R).inter_left (isClosed_le continuous_const Complex.continuous_im)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hc.mono Set.inter_subset_left)
  refine ⟨max B (max M 0 * Real.sqrt (1 + R) ^ 3), fun w hw => ?_⟩
  have hs : 0 < Real.sqrt (1 + ‖w‖) := Real.sqrt_pos.2 (by linarith [norm_nonneg w])
  by_cases hR : R ≤ ‖w‖
  · exact (hb w hw hR).trans (div_le_div_of_nonneg_right (le_max_left _ _) (pow_pos hs 3).le)
  · push Not at hR
    have h1 : ‖G w‖ ≤ M := hM w ⟨hw, by simpa using hR.le⟩
    have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hR.le
    have h2 : Real.sqrt (1 + ‖w‖) ≤ Real.sqrt (1 + R) := Real.sqrt_le_sqrt (by linarith)
    have h3 : max M 0 * Real.sqrt (1 + R) ^ 3 / Real.sqrt (1 + ‖w‖) ^ 3 ≥ max M 0 := by
      rw [ge_iff_le, le_div_iff₀ (pow_pos hs 3)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le h2 3) (le_max_right _ _)
    refine h1.trans ((le_max_left M 0).trans (h3.trans ?_))
    exact div_le_div_of_nonneg_right (le_max_right _ _) (pow_pos hs 3).le

theorem cauchy_conj_E02_38 (F : ℂ → ℂ) (C : ℝ)
    (hF : DifferentiableOn ℂ F {z | 0 < z.im}) (hc : ContinuousOn F {z | 0 ≤ z.im})
    (hdecay : ∀ w : ℂ, 0 ≤ w.im → ‖F w‖ ≤ C / Real.sqrt (1 + ‖w‖))
    (a : ℂ) (ha : a.im < 0) :
    Integrable (fun t : ℝ => F (t : ℂ) / ((t : ℂ) - a)) ∧
      ∫ t : ℝ, F (t : ℂ) / ((t : ℂ) - a) = 0 := by
  obtain ⟨K, hK1, hK⟩ := inv_dist_bound_E02_38 a ha
  have hne : ∀ w : ℂ, 0 ≤ w.im → w - a ≠ 0 := by
    intro w hw h
    have : (w - a).im = 0 := by rw [h]; simp
    simp at this; linarith
  have hC : 0 ≤ C := by
    have := hdecay 0 (by simp)
    simp at this
    exact le_trans (norm_nonneg _) this
  refine cauchy_decay_E02_38 (fun w => F w / (w - a)) (C * K) ?_ ?_ ?_
  · refine DifferentiableOn.div hF (differentiableOn_id.sub_const a) ?_
    intro w hw; exact hne w (le_of_lt hw)
  · refine hc.div (continuousOn_id.sub continuousOn_const) ?_
    intro w hw; exact hne w hw
  · intro w hw
    have hs : 0 < Real.sqrt (1 + ‖w‖) := Real.sqrt_pos.2 (by linarith [norm_nonneg w])
    have hpos : 0 < ‖w - a‖ := norm_pos_iff.2 (hne w hw)
    rw [norm_div]
    have h1 := hdecay w hw
    have h2 := hK w hw
    have h3 : 1 / ‖w - a‖ ≤ K / (1 + ‖w‖) := by
      rw [div_le_div_iff₀ hpos (by positivity)]; linarith
    calc ‖F w‖ / ‖w - a‖ = ‖F w‖ * (1 / ‖w - a‖) := by ring
      _ ≤ (C / Real.sqrt (1 + ‖w‖)) * (K / (1 + ‖w‖)) :=
          mul_le_mul h1 h3 (by positivity) (by positivity)
      _ = C * K / Real.sqrt (1 + ‖w‖) ^ 3 := by
          have e : K / (1 + ‖w‖) = K / Real.sqrt (1 + ‖w‖) ^ 2 := by rw [sqrt_sq_E02_38 w]
          rw [e]; field_simp


theorem cauchy_dslope_E02_38 (F : ℂ → ℂ) (C : ℝ)
    (hF : DifferentiableOn ℂ F {z | 0 < z.im}) (hc : ContinuousOn F {z | 0 ≤ z.im})
    (hdecay : ∀ w : ℂ, 0 ≤ w.im → ‖F w‖ ≤ C / Real.sqrt (1 + ‖w‖))
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun t : ℝ => (F (t : ℂ) - F z) / (((t : ℂ) - z) * ((t : ℂ) - (starRingEnd ℂ) z))) ∧
      ∫ t : ℝ, (F (t : ℂ) - F z) / (((t : ℂ) - z) * ((t : ℂ) - (starRingEnd ℂ) z)) = 0 := by
  set a : ℂ := (starRingEnd ℂ) z with ha_def
  have ha : a.im < 0 := by simp [ha_def, hz]
  obtain ⟨K, hK1, hK⟩ := inv_dist_bound_E02_38 a ha
  have hne : ∀ w : ℂ, 0 ≤ w.im → w - a ≠ 0 := by
    intro w hw h
    have : (w - a).im = 0 := by rw [h]; simp
    simp at this; linarith
  have hC : 0 ≤ C := by
    have := hdecay 0 (by simp)
    simp at this
    exact le_trans (norm_nonneg _) this
  have hopen : {w : ℂ | 0 < w.im} ∈ 𝓝 z := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
  have hdsd : DifferentiableOn ℂ (dslope F z) {w : ℂ | 0 < w.im} :=
    (Complex.differentiableOn_dslope hopen).2 hF
  have hdsc : ContinuousOn (dslope F z) {w : ℂ | 0 ≤ w.im} := by
    intro w hw
    by_cases hwz : w = z
    · subst hwz
      exact ((continuousAt_dslope_same).2 (hF.differentiableAt hopen)).continuousWithinAt
    · have h1 : ContinuousWithinAt (fun x => (F x - F z) / (x - z)) {w : ℂ | 0 ≤ w.im} w :=
        ((hc w hw).sub continuousWithinAt_const).div (continuousWithinAt_id.sub continuousWithinAt_const)
          (sub_ne_zero.2 hwz)
      refine h1.congr_of_eventuallyEq ?_ ?_
      · have : ∀ᶠ x in 𝓝 w, x ≠ z := isOpen_ne.mem_nhds hwz
        filter_upwards [nhdsWithin_le_nhds this] with x hx
        rw [dslope_of_ne _ hx, slope_def_field]
      · rw [dslope_of_ne _ hwz, slope_def_field]
  have hGd : DifferentiableOn ℂ (fun w => dslope F z w / (w - a)) {w : ℂ | 0 < w.im} :=
    DifferentiableOn.div hdsd (differentiableOn_id.sub_const a) (fun w hw => hne w (le_of_lt hw))
  have hGc : ContinuousOn (fun w => dslope F z w / (w - a)) {w : ℂ | 0 ≤ w.im} :=
    hdsc.div (continuousOn_id.sub continuousOn_const) (fun w hw => hne w hw)
  -- eventual bound
  set D := ‖F z‖ with hD
  have hbound : ∀ w : ℂ, 0 ≤ w.im → 2 * ‖z‖ + 2 ≤ ‖w‖ →
      ‖dslope F z w / (w - a)‖ ≤ (3 * K * (C + D)) / Real.sqrt (1 + ‖w‖) ^ 3 := by
    intro w hw hR
    have hs1 := sqrt_ge_one_E02_38 w
    have hs : 0 < Real.sqrt (1 + ‖w‖) := by linarith
    have e2 := sqrt_sq_E02_38 w
    have hwz : w ≠ z := by
      intro h; subst h; linarith [norm_nonneg w]
    have hu : (1 + ‖w‖) / 3 ≤ ‖w - z‖ := by
      have := norm_sub_norm_le w z
      linarith [norm_nonneg z, norm_nonneg w]
    have hv : (1 + ‖w‖) / K ≤ ‖w - a‖ := by
      rw [div_le_iff₀ (by linarith)]; linarith [hK w hw]
    have hFw : ‖F w - F z‖ ≤ C + D := by
      have h1 := hdecay w hw
      have h2 : C / Real.sqrt (1 + ‖w‖) ≤ C := div_le_self hC hs1
      calc ‖F w - F z‖ ≤ ‖F w‖ + ‖F z‖ := norm_sub_le _ _
        _ ≤ C + D := by linarith
    rw [dslope_of_ne _ hwz, slope_def_field, norm_div, norm_div]
    have hu0 : 0 < ‖w - z‖ := lt_of_lt_of_le (by positivity) hu
    have hK0 : 0 < K := by linarith
    have hv0 : 0 < ‖w - a‖ := lt_of_lt_of_le (by positivity) hv
    rw [div_div]
    have hCD : 0 ≤ C + D := by positivity
    have step : ‖F w - F z‖ / (‖w - z‖ * ‖w - a‖) ≤
        (C + D) / (((1 + ‖w‖) / 3) * ((1 + ‖w‖) / K)) := by
      apply div_le_div₀ hCD hFw (by positivity)
      exact mul_le_mul hu hv (by positivity) hu0.le
    refine step.trans ?_
    have e4 : ((1 + ‖w‖) / 3) * ((1 + ‖w‖) / K) = Real.sqrt (1 + ‖w‖) ^ 4 / (3 * K) := by
      rw [show Real.sqrt (1 + ‖w‖) ^ 4 = (Real.sqrt (1 + ‖w‖) ^ 2) ^ 2 by ring, e2]
      field_simp
    rw [e4]
    have : (3 * K * (C + D)) / Real.sqrt (1 + ‖w‖) ^ 3 ≥ (3 * K * (C + D)) / Real.sqrt (1 + ‖w‖) ^ 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (pow_pos hs 3)
      exact pow_le_pow_right₀ hs1 (by norm_num)
    refine le_trans (le_of_eq ?_) this
    field_simp
  obtain ⟨B', hB'⟩ := global_bound_E02_38 _ hGc _ _ hbound
  obtain ⟨hi, h0⟩ := cauchy_decay_E02_38 _ B' hGd hGc hB'
  have hpt : ∀ t : ℝ, dslope F z (t : ℂ) / ((t : ℂ) - a) =
      (F (t : ℂ) - F z) / (((t : ℂ) - z) * ((t : ℂ) - a)) := by
    intro t
    have hne' : (t : ℂ) ≠ z := by
      intro h
      have := congrArg Complex.im h
      simp at this; linarith
    rw [dslope_of_ne _ hne', slope_def_field, div_div]
  simp only [hpt] at hi h0
  exact ⟨hi, h0⟩


/-- Herglotz-type Cauchy representation in the upper half-plane for a function with
`‖F w‖ ≤ C / √(1 + ‖w‖)` that is holomorphic on `Im w > 0` and continuous on `Im w ≥ 0`:
`F z = (1/π) ∫ Im F(t) / (t - z) dt`, with absolutely convergent integral. -/
theorem halfPlane_herglotz_of_decay_E02_38 (F : ℂ → ℂ) (C : ℝ)
    (hF : DifferentiableOn ℂ F {z | 0 < z.im}) (hc : ContinuousOn F {z | 0 ≤ z.im})
    (hdecay : ∀ w : ℂ, 0 ≤ w.im → ‖F w‖ ≤ C / Real.sqrt (1 + ‖w‖)) :
    ∀ z : ℂ, 0 < z.im → Integrable (fun t : ℝ => ((F (t : ℂ)).im : ℂ) / ((t : ℂ) - z)) ∧
      F z = (1 / Real.pi : ℂ) * ∫ t : ℝ, ((F (t : ℂ)).im : ℂ) / ((t : ℂ) - z) := by
  intro z hz
  set a : ℂ := (starRingEnd ℂ) z with ha_def
  have ha : a.im < 0 := by simp [ha_def, hz]
  have hz0 : ∀ t : ℝ, (t : ℂ) - z ≠ 0 := by
    intro t h
    have := congrArg Complex.im h
    simp at this; linarith
  have ha0 : ∀ t : ℝ, (t : ℂ) - a ≠ 0 := by
    intro t h
    have := congrArg Complex.im h
    simp [ha_def] at this; linarith
  obtain ⟨hi3, h3⟩ := cauchy_conj_E02_38 F C hF hc hdecay a ha
  obtain ⟨hi2, h2⟩ := cauchy_dslope_E02_38 F C hF hc hdecay z hz
  obtain ⟨hik, hk⟩ := poisson_kernel_E02_38 z.re z.im hz
  -- the complex kernel
  have hkc : ∀ t : ℝ, 1 / (((t : ℂ) - z) * ((t : ℂ) - a)) =
      (((((t - z.re) ^ 2 + z.im ^ 2)⁻¹ : ℝ)) : ℂ) := by
    intro t
    have : ((t : ℂ) - z) * ((t : ℂ) - a) = (((t - z.re) ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [ha_def, sq] <;> ring
    rw [this]; push_cast; simp
  have hikc : Integrable (fun t : ℝ => 1 / (((t : ℂ) - z) * ((t : ℂ) - a))) := by
    simp only [hkc]
    exact hik.ofReal
  have hkint : ∫ t : ℝ, 1 / (((t : ℂ) - z) * ((t : ℂ) - a)) = ((Real.pi / z.im : ℝ) : ℂ) := by
    simp only [hkc]
    rw [integral_complex_ofReal, hk]
  -- F / ((t-z)(t-a))
  have hpt : ∀ t : ℝ, F (t : ℂ) / (((t : ℂ) - z) * ((t : ℂ) - a)) =
      (F (t : ℂ) - F z) / (((t : ℂ) - z) * ((t : ℂ) - a)) +
        F z * (1 / (((t : ℂ) - z) * ((t : ℂ) - a))) := by
    intro t; ring
  have hiP : Integrable (fun t : ℝ => F (t : ℂ) / (((t : ℂ) - z) * ((t : ℂ) - a))) := by
    simp only [hpt]; exact hi2.add (hikc.const_mul _)
  have hP : ∫ t : ℝ, F (t : ℂ) / (((t : ℂ) - z) * ((t : ℂ) - a)) = F z * ((Real.pi / z.im : ℝ) : ℂ) := by
    simp only [hpt]
    rw [integral_add hi2 (hikc.const_mul _), h2, integral_const_mul, hkint, zero_add]
  -- F/(t-z)
  have hpt2 : ∀ t : ℝ, F (t : ℂ) / ((t : ℂ) - z) = F (t : ℂ) / ((t : ℂ) - a) +
      (z - a) * (F (t : ℂ) / (((t : ℂ) - z) * ((t : ℂ) - a))) := by
    intro t
    have h1 := hz0 t; have h2 := ha0 t
    field_simp
    ring
  have hiz : Integrable (fun t : ℝ => F (t : ℂ) / ((t : ℂ) - z)) := by
    simp only [hpt2]; exact hi3.add (hiP.const_mul _)
  have hZ : ∫ t : ℝ, F (t : ℂ) / ((t : ℂ) - z) = 2 * Real.pi * I * F z := by
    simp only [hpt2]
    rw [integral_add hi3 (hiP.const_mul _), h3, integral_const_mul, hP, zero_add]
    have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have hza : z - a = 2 * I * (z.im : ℂ) := by
      apply Complex.ext <;> (simp [ha_def]; try ring)
    rw [hza]; push_cast; field_simp
  -- imaginary part
  have hpt3 : ∀ t : ℝ, ((F (t : ℂ)).im : ℂ) / ((t : ℂ) - z) =
      (1 / (2 * I)) * (F (t : ℂ) / ((t : ℂ) - z) -
        (starRingEnd ℂ) (F (t : ℂ) / ((t : ℂ) - a))) := by
    intro t
    have hconj : (starRingEnd ℂ) ((t : ℂ) - a) = (t : ℂ) - z := by
      simp [ha_def]
    rw [map_div₀, hconj, Complex.im_eq_sub_conj]
    field_simp
  have hic : Integrable (fun t : ℝ => (starRingEnd ℂ) (F (t : ℂ) / ((t : ℂ) - a))) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hi3
  have hiI : Integrable (fun t : ℝ => ((F (t : ℂ)).im : ℂ) / ((t : ℂ) - z)) := by
    simp only [hpt3]; exact (hiz.sub hic).const_mul _
  refine ⟨hiI, ?_⟩
  have hI : ∫ t : ℝ, ((F (t : ℂ)).im : ℂ) / ((t : ℂ) - z) = Real.pi * F z := by
    simp only [hpt3]
    rw [integral_const_mul, integral_sub hiz hic, hZ, integral_conj, h3]
    simp only [map_zero, sub_zero]
    field_simp
  rw [hI]
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end NlsGge.SpectralFoundations
