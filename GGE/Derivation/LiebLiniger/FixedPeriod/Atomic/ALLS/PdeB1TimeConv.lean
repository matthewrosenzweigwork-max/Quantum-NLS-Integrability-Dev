import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB1Bracket

/-! # Track B, step B1: the nonendpoint time-convolution estimate

Pro report, equation (timeconv): with `a = 13/32`,
`∫_ℝ ⟨λ⟩^{-2a} ⟨A - λ⟩^{-2a} dλ ≤ C ⟨A⟩^{1 - 4a}` for every real `A`.

We prove the general form for every exponent `s = 2a` with `1/2 < s < 1`
(`time_conv_bound`): the integrand is integrable for every `A` and the integral is at most
`C ⟨A⟩^{1-2s}` with one constant `C`. Pro's instance is `time_conv_bound_pro`.

Proof (Pro's region split, made explicit). For `|A| ≤ 2`, `xy ≤ x² + y²` and translation
invariance bound the integral by `2∫⟨λ⟩^{-2s}`. For `|A| ≥ 2` put `r = |A|/2`; then pointwise
`⟨λ⟩^{-s}⟨A-λ⟩^{-s}` is at most
`r^{-s} 1_{(-r,r]}(λ)⟨λ⟩^{-s} + r^{-s} 1_{(-r,r]}(λ-A)⟨λ-A⟩^{-s}
  + 1_{(-r,r]ᶜ}(λ)⟨λ⟩^{-2s} + 1_{(-r,r]ᶜ}(λ-A)⟨λ-A⟩^{-2s}`,
and the four integrals are `≤ 2r^{1-s}/(1-s)` (times `r^{-s}`) and `≤ 2r^{1-2s}/(2s-1)`.
Integrability is proved before every integral identity or comparison.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Set

/-- The bracket is continuous. -/
theorem continuous_brk : Continuous brk := by
  unfold brk
  fun_prop

/-- Every real power of the bracket is continuous. -/
theorem continuous_brk_rpow (q : ℝ) : Continuous fun x : ℝ => brk x ^ q :=
  continuous_brk.rpow_const fun x => Or.inl (brk_pos x).ne'

/-- `⟨x⟩` is at most `1 + |x|`. -/
theorem brk_le_one_add_abs (x : ℝ) : brk x ≤ 1 + |x| := by
  unfold brk
  calc Real.sqrt (1 + x ^ 2) ≤ Real.sqrt ((1 + |x|) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_abs x, abs_nonneg x])
    _ = 1 + |x| := Real.sqrt_sq (by positivity)

/-- `⟨x⟩^{-q}` is integrable on `ℝ` for `q > 1`. -/
theorem integrable_brk_rpow {q : ℝ} (hq : 1 < q) : Integrable fun x : ℝ => brk x ^ (-q) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := (volume : Measure ℝ)) (r := q)
    (by simpa using hq)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  unfold brk
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), Real.norm_eq_abs, sq_abs]
  congr 1
  ring

/-- `⟨x⟩^{-2q} = ⟨x⟩^{-q} ⟨x⟩^{-q}`. -/
theorem brk_rpow_two_mul (x q : ℝ) : brk x ^ (-(2 * q)) = brk x ^ (-q) * brk x ^ (-q) := by
  rw [← Real.rpow_add (brk_pos x)]
  congr 1
  ring

section Exponent

variable {s : ℝ}

/-- `∫_{(0,r]} ⟨x⟩^{-s} ≤ r^{1-s}/(1-s)` for `0 < s < 1`, `r ≥ 0`. -/
theorem integral_Ioc_zero_brk_rpow_le (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ} (hr : 0 ≤ r) :
    ∫ x in Ioc 0 r, brk x ^ (-s) ≤ r ^ (1 - s) / (1 - s) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (-s)) (Ioc 0 r) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r) (by linarith)).1
  have hb : IntegrableOn (fun x : ℝ => brk x ^ (-s)) (Ioc 0 r) :=
    (continuous_brk_rpow (-s)).integrableOn_Ioc
  calc ∫ x in Ioc 0 r, brk x ^ (-s)
      ≤ ∫ x in Ioc 0 r, x ^ (-s) :=
        setIntegral_mono_on hb hint measurableSet_Ioc fun x hx =>
          brk_rpow_neg_le_of_le hx.1 ((le_abs_self x).trans (abs_le_brk x)) hs0.le
    _ = r ^ (1 - s) / (1 - s) := by
        rw [← intervalIntegral.integral_of_le hr,
          integral_rpow (Or.inl (by linarith)),
          Real.zero_rpow (by linarith : -s + 1 ≠ 0), sub_zero]
        congr 1 <;> ring_nf

/-- `∫_{(-r,r]} ⟨x⟩^{-s} ≤ 2 r^{1-s}/(1-s)` for `0 < s < 1`, `r ≥ 0`. -/
theorem integral_Ioc_sym_brk_rpow_le (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ} (hr : 0 ≤ r) :
    ∫ x in Ioc (-r) r, brk x ^ (-s) ≤ 2 * (r ^ (1 - s) / (1 - s)) := by
  have hc := continuous_brk_rpow (-s)
  rw [← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hneg : ∫ x in (-r)..0, brk x ^ (-s) = ∫ x in (0 : ℝ)..r, brk x ^ (-s) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := r) (fun x : ℝ => brk x ^ (-s))
    simp only [brk_neg, neg_zero] at this
    exact this.symm
  rw [hneg, intervalIntegral.integral_of_le hr]
  linarith [integral_Ioc_zero_brk_rpow_le hs0 hs1 hr]

/-- Tail: `∫_{(r,∞)} ⟨x⟩^{-2s} ≤ r^{1-2s}/(2s-1)` for `s > 1/2`, `r > 0`. -/
theorem integral_Ioi_brk_rpow_le (hs : 1 / 2 < s) {r : ℝ} (hr : 0 < r) :
    ∫ x in Ioi r, brk x ^ (-(2 * s)) ≤ r ^ (1 - 2 * s) / (2 * s - 1) := by
  have hlt : -(2 * s) < -1 := by linarith
  calc ∫ x in Ioi r, brk x ^ (-(2 * s))
      ≤ ∫ x in Ioi r, x ^ (-(2 * s)) :=
        setIntegral_mono_on (integrable_brk_rpow (by linarith)).integrableOn
          (integrableOn_Ioi_rpow_of_lt hlt hr) measurableSet_Ioi fun x hx =>
          brk_rpow_neg_le_of_le (hr.trans hx) ((le_abs_self x).trans (abs_le_brk x))
            (by linarith)
    _ = r ^ (1 - 2 * s) / (2 * s - 1) := by
        rw [integral_Ioi_rpow_of_lt hlt hr]
        have h1 : -(2 * s) + 1 = 1 - 2 * s := by ring
        rw [h1, neg_div, ← div_neg]
        congr 1
        ring

/-- Two-sided tail: `∫_{(-r,r]ᶜ} ⟨x⟩^{-2s} ≤ 2 r^{1-2s}/(2s-1)`. -/
theorem integral_compl_brk_rpow_le (hs : 1 / 2 < s) {r : ℝ} (hr : 0 < r) :
    ∫ x in (Ioc (-r) r)ᶜ, brk x ^ (-(2 * s)) ≤ 2 * (r ^ (1 - 2 * s) / (2 * s - 1)) := by
  have hI := integrable_brk_rpow (q := 2 * s) (by linarith)
  rw [compl_Ioc, setIntegral_union (Iic_disjoint_Ioi (by linarith)) measurableSet_Ioi
    hI.integrableOn hI.integrableOn]
  have hneg : ∫ x in Iic (-r), brk x ^ (-(2 * s)) = ∫ x in Ioi r, brk x ^ (-(2 * s)) := by
    have := integral_comp_neg_Ioi r (fun x : ℝ => brk x ^ (-(2 * s)))
    simp only [brk_neg] at this
    exact this.symm
  rw [hneg]
  linarith [integral_Ioi_brk_rpow_le hs hr]

/-- The integrand `⟨λ⟩^{-s} ⟨A-λ⟩^{-s}`. -/
def timeConvIntegrand (s A t : ℝ) : ℝ := brk t ^ (-s) * brk (A - t) ^ (-s)

/-- AM–GM majorant: `⟨λ⟩^{-s}⟨A-λ⟩^{-s} ≤ ⟨λ⟩^{-2s} + ⟨λ-A⟩^{-2s}`. -/
theorem timeConvIntegrand_le_sum (s A t : ℝ) :
    timeConvIntegrand s A t ≤ brk t ^ (-(2 * s)) + brk (t - A) ^ (-(2 * s)) := by
  unfold timeConvIntegrand
  rw [brk_rpow_two_mul, brk_rpow_two_mul, show t - A = -(A - t) by ring, brk_neg]
  have h1 := brk_rpow_nonneg t (-s)
  have h2 := brk_rpow_nonneg (A - t) (-s)
  nlinarith [sq_nonneg (brk t ^ (-s) - brk (A - t) ^ (-s))]

/-- The integrand is integrable for every `A` (`s > 1/2`). -/
theorem integrable_timeConvIntegrand (hs : 1 / 2 < s) (A : ℝ) :
    Integrable (timeConvIntegrand s A) := by
  have hI := integrable_brk_rpow (q := 2 * s) (by linarith)
  refine (hI.add (hI.comp_sub_right A)).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((continuous_brk_rpow (-s)).mul
      ((continuous_brk_rpow (-s)).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold timeConvIntegrand; exact mul_nonneg (brk_rpow_nonneg _ _) (brk_rpow_nonneg _ _))]
    exact timeConvIntegrand_le_sum s A t

/-- Bounded `A`: `∫ ≤ 2 ∫ ⟨x⟩^{-2s}`. -/
theorem integral_timeConvIntegrand_le_small (hs : 1 / 2 < s) (A : ℝ) :
    ∫ t, timeConvIntegrand s A t ≤ 2 * ∫ x, brk x ^ (-(2 * s)) := by
  have hI := integrable_brk_rpow (q := 2 * s) (by linarith)
  calc ∫ t, timeConvIntegrand s A t
      ≤ ∫ t, (brk t ^ (-(2 * s)) + brk (t - A) ^ (-(2 * s))) :=
        integral_mono (integrable_timeConvIntegrand hs A) (hI.add (hI.comp_sub_right A))
          (timeConvIntegrand_le_sum s A)
    _ = 2 * ∫ x, brk x ^ (-(2 * s)) := by
        rw [integral_add hI (hI.comp_sub_right A),
          integral_sub_right_eq_self (fun x => brk x ^ (-(2 * s))) A]
        ring

/-- The three-region pointwise majorant for `|A| ≥ 2r`, `r > 0`. -/
theorem timeConvIntegrand_le_regions (hs0 : 0 < s) {r A : ℝ} (hr : 0 < r) (hA : 2 * r ≤ |A|)
    (t : ℝ) :
    timeConvIntegrand s A t ≤
      r ^ (-s) * (Ioc (-r) r).indicator (fun x => brk x ^ (-s)) t +
        r ^ (-s) * (Ioc (-r) r).indicator (fun x => brk x ^ (-s)) (t - A) +
        (Ioc (-r) r)ᶜ.indicator (fun x => brk x ^ (-(2 * s))) t +
        (Ioc (-r) r)ᶜ.indicator (fun x => brk x ^ (-(2 * s))) (t - A) := by
  unfold timeConvIntegrand
  have hsym : brk (A - t) = brk (t - A) := by rw [show A - t = -(t - A) by ring, brk_neg]
  have hn1 := brk_rpow_nonneg t (-s)
  have hn2 := brk_rpow_nonneg (t - A) (-s)
  have hrs : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr.le _
  have i1 : 0 ≤ (Ioc (-r) r).indicator (fun x => brk x ^ (-s)) t :=
    Set.indicator_nonneg (fun x _ => brk_rpow_nonneg x _) t
  have i2 : 0 ≤ (Ioc (-r) r).indicator (fun x => brk x ^ (-s)) (t - A) :=
    Set.indicator_nonneg (fun x _ => brk_rpow_nonneg x _) (t - A)
  have i3 : 0 ≤ (Ioc (-r) r)ᶜ.indicator (fun x => brk x ^ (-(2 * s))) t :=
    Set.indicator_nonneg (fun x _ => brk_rpow_nonneg x _) t
  have i4 : 0 ≤ (Ioc (-r) r)ᶜ.indicator (fun x => brk x ^ (-(2 * s))) (t - A) :=
    Set.indicator_nonneg (fun x _ => brk_rpow_nonneg x _) (t - A)
  by_cases h1 : t ∈ Ioc (-r) r
  · -- `|t| ≤ r`, hence `|A - t| ≥ r`
    have ht : |t| ≤ r := abs_le.2 ⟨h1.1.le, h1.2⟩
    have hAt : r ≤ brk (A - t) := by
      refine le_trans ?_ (abs_le_brk _)
      have := abs_sub_abs_le_abs_sub A t
      linarith
    have hb : brk (A - t) ^ (-s) ≤ r ^ (-s) := brk_rpow_neg_le_of_le hr hAt hs0.le
    rw [Set.indicator_of_mem h1]
    nlinarith
  by_cases h2 : t - A ∈ Ioc (-r) r
  · have ht : |t - A| ≤ r := abs_le.2 ⟨h2.1.le, h2.2⟩
    have hAt : r ≤ brk t := by
      refine le_trans ?_ (abs_le_brk _)
      have := abs_sub_abs_le_abs_sub A (A - t)
      rw [show A - (A - t) = t by ring, show A - t = -(t - A) by ring, abs_neg] at this
      linarith
    have hb : brk t ^ (-s) ≤ r ^ (-s) := brk_rpow_neg_le_of_le hr hAt hs0.le
    rw [Set.indicator_of_mem h2, hsym]
    nlinarith
  · rw [Set.indicator_of_mem (show t ∈ (Ioc (-r) r)ᶜ from h1),
      Set.indicator_of_mem (show t - A ∈ (Ioc (-r) r)ᶜ from h2),
      brk_rpow_two_mul, brk_rpow_two_mul, hsym]
    nlinarith [sq_nonneg (brk t ^ (-s) - brk (t - A) ^ (-s)), mul_nonneg hrs i1,
      mul_nonneg hrs i2]

/-- Large `A`: `∫ ≤ K r^{1-2s}` with `r = |A|/2 ≥ 1`. -/
theorem integral_timeConvIntegrand_le_large (hs : 1 / 2 < s) (hs1 : s < 1) {A : ℝ}
    (hA : 2 ≤ |A|) :
    ∫ t, timeConvIntegrand s A t ≤
      (4 / (1 - s) + 4 / (2 * s - 1)) * (|A| / 2) ^ (1 - 2 * s) := by
  have hs0 : 0 < s := by linarith
  set r := |A| / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hrA : 2 * r ≤ |A| := by rw [hrdef]; linarith
  have hc1 := continuous_brk_rpow (-s)
  have hI1 : Integrable ((Ioc (-r) r).indicator fun x => brk x ^ (-s)) :=
    hc1.integrableOn_Ioc.integrable_indicator measurableSet_Ioc
  have hI2 : Integrable ((Ioc (-r) r)ᶜ.indicator fun x => brk x ^ (-(2 * s))) :=
    (integrable_brk_rpow (q := 2 * s) (by linarith)).integrableOn.integrable_indicator
      measurableSet_Ioc.compl
  have hmaj : Integrable fun t =>
      r ^ (-s) * (Ioc (-r) r).indicator (fun x => brk x ^ (-s)) t +
        r ^ (-s) * (Ioc (-r) r).indicator (fun x => brk x ^ (-s)) (t - A) +
        (Ioc (-r) r)ᶜ.indicator (fun x => brk x ^ (-(2 * s))) t +
        (Ioc (-r) r)ᶜ.indicator (fun x => brk x ^ (-(2 * s))) (t - A) :=
    (((hI1.const_mul _).add ((hI1.comp_sub_right A).const_mul _)).add hI2).add
      (hI2.comp_sub_right A)
  have hval1 : ∫ x, (Ioc (-r) r).indicator (fun x => brk x ^ (-s)) x ≤
      2 * (r ^ (1 - s) / (1 - s)) := by
    rw [integral_indicator measurableSet_Ioc]
    exact integral_Ioc_sym_brk_rpow_le hs0 hs1 hr.le
  have hval2 : ∫ x, (Ioc (-r) r)ᶜ.indicator (fun x => brk x ^ (-(2 * s))) x ≤
      2 * (r ^ (1 - 2 * s) / (2 * s - 1)) := by
    rw [integral_indicator measurableSet_Ioc.compl]
    exact integral_compl_brk_rpow_le hs hr
  have hpow : r ^ (-s) * r ^ (1 - s) = r ^ (1 - 2 * s) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have hrs : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr.le _
  calc ∫ t, timeConvIntegrand s A t
      ≤ ∫ t, (r ^ (-s) * (Ioc (-r) r).indicator (fun x => brk x ^ (-s)) t +
          r ^ (-s) * (Ioc (-r) r).indicator (fun x => brk x ^ (-s)) (t - A) +
          (Ioc (-r) r)ᶜ.indicator (fun x => brk x ^ (-(2 * s))) t +
          (Ioc (-r) r)ᶜ.indicator (fun x => brk x ^ (-(2 * s))) (t - A)) :=
        integral_mono (integrable_timeConvIntegrand hs A) hmaj
          (timeConvIntegrand_le_regions hs0 hr hrA)
    _ = 2 * (r ^ (-s) * ∫ x, (Ioc (-r) r).indicator (fun x => brk x ^ (-s)) x) +
          2 * ∫ x, (Ioc (-r) r)ᶜ.indicator (fun x => brk x ^ (-(2 * s))) x := by
        set I1 := (Ioc (-r) r).indicator (fun x => brk x ^ (-s)) with hI1def
        set I2 := (Ioc (-r) r)ᶜ.indicator (fun x => brk x ^ (-(2 * s))) with hI2def
        have hf1 : Integrable (fun t => r ^ (-s) * I1 t) := hI1.const_mul _
        have hf2 : Integrable (fun t => r ^ (-s) * I1 (t - A)) :=
          (hI1.comp_sub_right A).const_mul _
        have hf3 : Integrable (fun t => I2 t) := hI2
        have hf4 : Integrable (fun t => I2 (t - A)) := hI2.comp_sub_right A
        have h12 : Integrable (fun t => r ^ (-s) * I1 t + r ^ (-s) * I1 (t - A)) := hf1.add hf2
        have h123 : Integrable
            (fun t => r ^ (-s) * I1 t + r ^ (-s) * I1 (t - A) + I2 t) := h12.add hf3
        rw [integral_add h123 hf4, integral_add h12 hf3, integral_add hf1 hf2,
          integral_const_mul, integral_const_mul, integral_sub_right_eq_self I1 A,
          integral_sub_right_eq_self I2 A]
        ring
    _ ≤ 2 * (r ^ (-s) * (2 * (r ^ (1 - s) / (1 - s)))) +
          2 * (2 * (r ^ (1 - 2 * s) / (2 * s - 1))) := by
        gcongr
    _ = (4 / (1 - s) + 4 / (2 * s - 1)) * r ^ (1 - 2 * s) := by
        rw [show r ^ (-s) * (2 * (r ^ (1 - s) / (1 - s))) =
            2 * (r ^ (-s) * r ^ (1 - s)) / (1 - s) by ring, hpow]
        ring

end Exponent

/-- **Nonendpoint time convolution** (Pro, eq. (timeconv), general form): for `1/2 < s < 1`
there is one constant `C` such that for every real `A` the function
`λ ↦ ⟨λ⟩^{-s}⟨A-λ⟩^{-s}` is integrable and its integral is at most `C ⟨A⟩^{1-2s}`. -/
theorem time_conv_bound {s : ℝ} (hs : 1 / 2 < s) (hs1 : s < 1) :
    ∃ C : ℝ, ∀ A : ℝ,
      Integrable (fun t : ℝ => brk t ^ (-s) * brk (A - t) ^ (-s)) ∧
        ∫ t, brk t ^ (-s) * brk (A - t) ^ (-s) ≤ C * brk A ^ (1 - 2 * s) := by
  have hexp : 1 - 2 * s ≤ 0 := by linarith
  set J := ∫ x, brk x ^ (-(2 * s)) with hJ
  set K := 4 / (1 - s) + 4 / (2 * s - 1) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have : 0 < 1 - s := by linarith
    have : 0 < 2 * s - 1 := by linarith
    positivity
  have hJ0 : 0 ≤ J := integral_nonneg fun x => brk_rpow_nonneg _ _
  refine ⟨max (2 * J / brk 2 ^ (1 - 2 * s)) (K / 4 ^ (1 - 2 * s)), fun A => ?_⟩
  refine ⟨integrable_timeConvIntegrand hs A, ?_⟩
  change ∫ t, timeConvIntegrand s A t ≤ _
  have hbA := brk_pos A
  have hpA : 0 < brk A ^ (1 - 2 * s) := Real.rpow_pos_of_pos hbA _
  rcases le_or_gt |A| 2 with hA | hA
  · have hb2 : 0 < brk 2 ^ (1 - 2 * s) := Real.rpow_pos_of_pos (brk_pos 2) _
    have hmono : brk 2 ^ (1 - 2 * s) ≤ brk A ^ (1 - 2 * s) :=
      Real.rpow_le_rpow_of_nonpos hbA (brk_le_brk (by rwa [abs_of_pos (by norm_num : (0:ℝ) < 2)]))
        hexp
    calc ∫ t, timeConvIntegrand s A t ≤ 2 * J := integral_timeConvIntegrand_le_small hs A
      _ = 2 * J / brk 2 ^ (1 - 2 * s) * brk 2 ^ (1 - 2 * s) := by field_simp
      _ ≤ 2 * J / brk 2 ^ (1 - 2 * s) * brk A ^ (1 - 2 * s) := by
          gcongr
      _ ≤ max (2 * J / brk 2 ^ (1 - 2 * s)) (K / 4 ^ (1 - 2 * s)) * brk A ^ (1 - 2 * s) := by
          gcongr; exact le_max_left _ _
  · have hr : 0 < |A| / 2 := by linarith
    have hbr : brk A / 4 ≤ |A| / 2 := by
      have := brk_le_one_add_abs A
      linarith
    have hbr0 : 0 < brk A / 4 := by positivity
    have hpow : (|A| / 2) ^ (1 - 2 * s) ≤ (brk A / 4) ^ (1 - 2 * s) :=
      Real.rpow_le_rpow_of_nonpos hbr0 hbr hexp
    have h4 : 0 < (4 : ℝ) ^ (1 - 2 * s) := Real.rpow_pos_of_pos (by norm_num) _
    calc ∫ t, timeConvIntegrand s A t ≤ K * (|A| / 2) ^ (1 - 2 * s) :=
          integral_timeConvIntegrand_le_large hs hs1 hA.le
      _ ≤ K * (brk A / 4) ^ (1 - 2 * s) := by gcongr
      _ = K / 4 ^ (1 - 2 * s) * brk A ^ (1 - 2 * s) := by
          rw [Real.div_rpow hbA.le (by norm_num)]
          ring
      _ ≤ max (2 * J / brk 2 ^ (1 - 2 * s)) (K / 4 ^ (1 - 2 * s)) * brk A ^ (1 - 2 * s) := by
          gcongr; exact le_max_right _ _

/-- Pro's instance of (timeconv): `a = 13/32`, i.e. `∫⟨λ⟩^{-2a}⟨A-λ⟩^{-2a} ≤ C⟨A⟩^{1-4a}`. -/
theorem time_conv_bound_pro :
    ∃ C : ℝ, ∀ A : ℝ,
      Integrable (fun t : ℝ => brk t ^ (-(2 * (13 / 32 : ℝ))) * brk (A - t) ^ (-(2 * (13 / 32 : ℝ)))) ∧
        ∫ t, brk t ^ (-(2 * (13 / 32 : ℝ))) * brk (A - t) ^ (-(2 * (13 / 32 : ℝ))) ≤
          C * brk A ^ (1 - 4 * (13 / 32 : ℝ)) := by
  obtain ⟨C, hC⟩ := time_conv_bound (s := 2 * (13 / 32 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨C, fun A => ⟨(hC A).1, ?_⟩⟩
  have h := (hC A).2
  rwa [show (1 : ℝ) - 2 * (2 * (13 / 32 : ℝ)) = 1 - 4 * (13 / 32 : ℝ) by ring] at h

end LiebLiniger.FixedPeriod.ALLS.PdeB
