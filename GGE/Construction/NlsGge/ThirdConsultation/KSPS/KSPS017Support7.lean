import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support2
import NlsGge.ThirdConsultation.KSPS.KSPS012Support5

                                                                                                                    
                                                                                                               
                                                                                        
                                                                                                
                                                                                                           
                                                                          
                                                                                                           
                                                                                                             
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Interval

namespace NlsGge.ThirdConsultation.KSPS017W
noncomputable section

theorem norm_exp_strip {ζ : ℂ} {A : ℝ} (hζ : |ζ.im| ≤ A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (sgn : ℝ)
    (hsgn : |sgn| ≤ 1) : ‖Complex.exp (sgn * (2 * Complex.I * ζ * (s : ℂ)))‖ ≤ Real.exp (2 * A) :=
  NlsGge.ThirdConsultation.KSPS012Support5.norm_exp_mul_real_le hζ hs sgn hsgn

theorem im_le_of_ball {ζ ζ0 : ℂ} (h : ζ ∈ Metric.ball ζ0 1) : |ζ.im| ≤ |ζ0.im| + 1 := by
  have h1 : |ζ.im - ζ0.im| ≤ ‖ζ - ζ0‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  have h2 : ‖ζ - ζ0‖ < 1 := by rw [← dist_eq_norm]; exact h
  have h3 := abs_sub_abs_le_abs_sub ζ.im ζ0.im
  linarith

theorem hasDerivAt_Dd {d : ℝ → ℂ} (hd : IntervalIntegrable d volume 0 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ζ0 : ℂ) :
    HasDerivAt (fun ζ : ℂ => ∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s)
      (∫ s in t..1, Complex.exp (2 * Complex.I * ζ0 * (s : ℂ)) * (2 * Complex.I * (s : ℂ) * d s)) ζ0 := by
  have hsub : [[t, (1 : ℝ)]] ⊆ [[(0 : ℝ), 1]] := by
    rw [uIcc_of_le ht.2, uIcc_of_le zero_le_one]; exact Icc_subset_Icc ht.1 le_rfl
  have hdt : IntervalIntegrable d volume t 1 := hd.mono_set hsub
  have hdm : AEStronglyMeasurable d (volume.restrict (Ι t 1)) := hdt.def'.aestronglyMeasurable
  have hI : ∀ s ∈ Ι t 1, s ∈ Icc (0 : ℝ) 1 := by
    intro s hs; rw [uIoc_of_le ht.2] at hs; exact ⟨ht.1.trans hs.1.le, hs.2⟩
  have hc : ∀ ζ : ℂ, Continuous (fun s : ℝ => Complex.exp (2 * Complex.I * ζ * (s : ℂ))) :=
    fun ζ => by fun_prop
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun ζ s => Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s)
    (F' := fun ζ s => Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * (2 * Complex.I * (s : ℂ) * d s))
    (x₀ := ζ0) (s := Metric.ball ζ0 1) (bound := fun s => Real.exp (2 * (|ζ0.im| + 1)) * (2 * ‖d s‖))
    (Metric.ball_mem_nhds ζ0 one_pos)
    (Eventually.of_forall (fun ζ => (hc ζ).aestronglyMeasurable.mul hdm))
    (hdt.continuousOn_mul (hc ζ0).continuousOn)
    ((hc ζ0).aestronglyMeasurable.mul ((by fun_prop : Continuous (fun s : ℝ =>
      2 * Complex.I * (s : ℂ))).aestronglyMeasurable.mul hdm))
    (Eventually.of_forall (fun s hs ζ hζ => by
      have hs' := hI s hs
      have he : ‖Complex.exp (2 * Complex.I * ζ * (s : ℂ))‖ ≤ Real.exp (2 * (|ζ0.im| + 1)) := by
        simpa using norm_exp_strip (im_le_of_ball hζ) hs' 1 (by norm_num)
      have h2 : ‖2 * Complex.I * (s : ℂ)‖ ≤ 2 := by
        rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hs'.1]
        linarith [hs'.2]
      rw [norm_mul, norm_mul]
      calc ‖Complex.exp (2 * Complex.I * ζ * (s : ℂ))‖ * (‖2 * Complex.I * (s : ℂ)‖ * ‖d s‖)
          ≤ Real.exp (2 * (|ζ0.im| + 1)) * (2 * ‖d s‖) := by gcongr))
    ((hdt.norm.const_mul 2).const_mul _)
    (Eventually.of_forall (fun s _ ζ _ => by
      have hd1 : HasDerivAt (fun y : ℂ => 2 * Complex.I * y * (s : ℂ)) (2 * Complex.I * 1 * (s : ℂ)) ζ :=
        ((hasDerivAt_id ζ).const_mul (2 * Complex.I)).mul_const _
      refine (hd1.cexp.mul_const (d s)).congr_deriv ?_
      ring))
  exact h.2

theorem Dd_aesm {d : ℝ → ℂ} (hd : IntervalIntegrable d volume 0 1) (ζ : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => ∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
  rw [uIoc_of_le zero_le_one]
  exact ((NlsGge.ThirdConsultation.KSPS012Support5.Dd_continuousOn hd ζ).mono Ioc_subset_Icc_self).aestronglyMeasurable
    measurableSet_Ioc

theorem hasDerivAt_Tz {c d : ℝ → ℂ} (hc : IntervalIntegrable c volume 0 1)
    (hd : IntervalIntegrable d volume 0 1) (ζ0 : ℂ) :
    HasDerivAt (NlsGge.ThirdConsultation.KSPS012Support5.Tz c d)
      (2 * Complex.I * (NlsGge.ThirdConsultation.KSPS012Support5.Tz c (fun s => (s : ℂ) * d s) ζ0 -
        NlsGge.ThirdConsultation.KSPS012Support5.Tz (fun t => (t : ℂ) * c t) d ζ0)) ζ0 := by
  set d' : ℝ → ℂ := fun s => 2 * Complex.I * (s : ℂ) * d s with hd'def
  have hd' : IntervalIntegrable d' volume 0 1 :=
    hd.continuousOn_mul (by fun_prop : Continuous fun s : ℝ => 2 * Complex.I * (s : ℂ)).continuousOn
  have hcm : AEStronglyMeasurable c (volume.restrict (Ι (0 : ℝ) 1)) := hc.def'.aestronglyMeasurable
  have hce : ∀ ζ : ℂ, Continuous (fun t : ℝ => Complex.exp (-(2 * Complex.I * ζ * (t : ℂ)))) :=
    fun ζ => by fun_prop
  set A : ℝ := Real.exp (2 * (|ζ0.im| + 1)) with hA
  set Ld : ℝ := ∫ s in (0 : ℝ)..1, ‖d s‖ with hLd
  set Ld' : ℝ := ∫ s in (0 : ℝ)..1, ‖d' s‖ with hLd'
  have hLd0 : 0 ≤ Ld := intervalIntegral.integral_nonneg zero_le_one (fun s _ => norm_nonneg _)
  have hLd'0 : 0 ≤ Ld' := intervalIntegral.integral_nonneg zero_le_one (fun s _ => norm_nonneg _)
  have hI : ∀ t ∈ Ι (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht; rw [uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le, ht.2⟩
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun ζ t => (Complex.exp (-(2 * Complex.I * ζ * (t : ℂ))) * c t) *
      ∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s)
    (F' := fun ζ t => (Complex.exp (-(2 * Complex.I * ζ * (t : ℂ))) * c t) *
      (-(2 * Complex.I * (t : ℂ)) * (∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s) +
        ∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d' s))
    (x₀ := ζ0) (s := Metric.ball ζ0 1) (bound := fun t => A * ‖c t‖ * (2 * (A * Ld) + A * Ld'))
    (Metric.ball_mem_nhds ζ0 one_pos)
    (Eventually.of_forall (fun ζ =>
      (NlsGge.ThirdConsultation.KSPS012Support5.Tz_integrable hc hd ζ).def'.aestronglyMeasurable))
    (NlsGge.ThirdConsultation.KSPS012Support5.Tz_integrable hc hd ζ0)
    (((hce ζ0).aestronglyMeasurable.mul hcm).mul
      (((by fun_prop : Continuous fun t : ℝ => -(2 * Complex.I * (t : ℂ))).aestronglyMeasurable.mul
        (Dd_aesm hd ζ0)).add (Dd_aesm hd' ζ0)))
    (Eventually.of_forall (fun t ht ζ hζ => by
      have ht' := hI t ht
      have him := im_le_of_ball hζ
      have he : ‖Complex.exp (-(2 * Complex.I * ζ * (t : ℂ)))‖ ≤ A := by
        simpa using norm_exp_strip him ht' (-1) (by norm_num)
      have hD : ‖∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s‖ ≤ A * Ld :=
        NlsGge.ThirdConsultation.KSPS012Support5.Dd_norm_le hd him ht'
      have hD' : ‖∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d' s‖ ≤ A * Ld' :=
        NlsGge.ThirdConsultation.KSPS012Support5.Dd_norm_le hd' him ht'
      have h2 : ‖-(2 * Complex.I * (t : ℂ))‖ ≤ 2 := by
        rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ht'.1]
        linarith [ht'.2]
      have hsum : ‖-(2 * Complex.I * (t : ℂ)) * (∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s) +
          ∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d' s‖ ≤ 2 * (A * Ld) + A * Ld' := by
        refine (norm_add_le _ _).trans (add_le_add ?_ hD')
        rw [norm_mul]; exact mul_le_mul h2 hD (norm_nonneg _) (by norm_num)
      rw [norm_mul, norm_mul]
      calc ‖Complex.exp (-(2 * Complex.I * ζ * (t : ℂ)))‖ * ‖c t‖ *
            ‖-(2 * Complex.I * (t : ℂ)) * (∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s) +
              ∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d' s‖
          ≤ A * ‖c t‖ * (2 * (A * Ld) + A * Ld') := by gcongr))
    ((hc.norm.const_mul A).mul_const _)
    (Eventually.of_forall (fun t ht ζ _ => by
      have ht' := hI t ht
      have he : HasDerivAt (fun y : ℂ => Complex.exp (-(2 * Complex.I * y * (t : ℂ))) * c t)
          (Complex.exp (-(2 * Complex.I * ζ * (t : ℂ))) * (-(2 * Complex.I * 1 * (t : ℂ))) * c t) ζ :=
        ((((hasDerivAt_id ζ).const_mul (2 * Complex.I)).mul_const (t : ℂ)).neg.cexp).mul_const (c t)
      refine (he.mul (hasDerivAt_Dd hd ht' ζ)).congr_deriv ?_
      simp only [hd'def]
      ring))
  -- identify the derivative
  have hTi := NlsGge.ThirdConsultation.KSPS012Support5.Tz_integrable (c := c)
    (d := fun s => (s : ℂ) * d s) hc
    (hd.continuousOn_mul (by fun_prop : Continuous fun s : ℝ => (s : ℂ)).continuousOn) ζ0
  have hTt := NlsGge.ThirdConsultation.KSPS012Support5.Tz_integrable (c := fun t => (t : ℂ) * c t) (d := d)
    (hc.continuousOn_mul (by fun_prop : Continuous fun t : ℝ => (t : ℂ)).continuousOn) hd ζ0
  refine h.2.congr_deriv ?_
  unfold NlsGge.ThirdConsultation.KSPS012Support5.Tz
  rw [mul_sub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hTi.const_mul _) (hTt.const_mul _)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  have hin : (∫ s in t..1, Complex.exp (2 * Complex.I * ζ0 * (s : ℂ)) * d' s) =
      2 * Complex.I * ∫ s in t..1, Complex.exp (2 * Complex.I * ζ0 * (s : ℂ)) * ((s : ℂ) * d s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [hd'def]; ring
  beta_reduce
  rw [hin]
  ring

theorem Tz_seq_sq_summable {c d : ℝ → ℂ} (hcm : AEStronglyMeasurable c volume)
    (hc1 : IntervalIntegrable c volume 0 1)
    (hc2 : IntervalIntegrable (fun t => ‖c t‖ ^ 2) volume 0 1)
    (hd : IntervalIntegrable d volume 0 1) (a : ℝ) (ha : 0 ≤ a) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / Real.sqrt (1 + (n : ℝ) ^ 2))
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    Summable (fun n : ℤ => ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n)‖ ^ 2) := by
  have h := NlsGge.ThirdConsultation.KSPS012Support2.T_sq_summable hcm hc1 hc2 hd
  have hk : ∀ k : ℤ, NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((k : ℂ) * (Real.pi : ℂ)) =
      ∫ t in (0 : ℝ)..1, (Complex.exp (-(2 * Real.pi * Complex.I * k * t)) * c t) *
        ∫ s in t..1, Complex.exp (2 * Real.pi * Complex.I * k * s) * d s := by
    intro k
    unfold NlsGge.ThirdConsultation.KSPS012Support5.Tz
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have e1 : Complex.exp (-(2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (t : ℂ))) =
        Complex.exp (-(2 * Real.pi * Complex.I * k * t)) := by congr 1; ring
    have e2 : ∫ s in t..1, Complex.exp (2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) * d s =
        ∫ s in t..1, Complex.exp (2 * Real.pi * Complex.I * k * s) * d s := by
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      have : Complex.exp (2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) =
          Complex.exp (2 * Real.pi * Complex.I * k * s) := by congr 1; ring
      rw [this]
    rw [e1, e2]
  have hs : Summable (fun k : ℤ => ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d
      ((k : ℂ) * (Real.pi : ℂ))‖ ^ 2) := h.congr (fun k => by rw [hk k])
  have hsσ : Summable (fun n : ℤ => ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d
      (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖ ^ 2) := by
    rcases hσ with rfl | rfl
    · simpa using hs
    · have := hs.comp_injective neg_injective
      refine this.congr (fun n => ?_)
      simp
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * (Real.exp (2 * a) + 1) * (∫ s in (0 : ℝ)..1, ‖d s‖) *
      ∫ t in (0 : ℝ)..1, ‖c t‖ := ⟨_, rfl⟩
  have hS1 : Summable (fun n : ℤ => (1 / |(n : ℝ)|) ^ 2) := by
    have h0 := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
    refine h0.congr (fun n => ?_)
    rw [div_pow, one_pow, sq_abs]
  have hdom : Summable (fun n : ℤ => (‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d
      (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖ + K * a * (1 / |(n : ℝ)|)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) ((hsσ.mul_left 2).add
      ((hS1.mul_left ((K * a) ^ 2)).mul_left 2))
    have := sq_nonneg (‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d
      (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖ - K * a * (1 / |(n : ℝ)|))
    nlinarith
  refine Summable.of_norm_bounded_eventually hdom ?_
  have hev : ∀ᶠ n : ℤ in cofinite, ((⌈2 * a⌉₊ + 1 : ℕ) : ℤ) ≤ |n| := by
    rw [Filter.eventually_cofinite]
    apply (Set.finite_Icc (-(((⌈2 * a⌉₊ + 1 : ℕ) : ℤ))) ((⌈2 * a⌉₊ + 1 : ℕ) : ℤ)).subset
    intro n hn
    simp only [Set.mem_setOf_eq, not_le] at hn
    rw [Set.mem_Icc]
    constructor <;> cases abs_cases n <;> omega
  filter_upwards [hev] with n hn
  have hnR : ((⌈2 * a⌉₊ + 1 : ℕ) : ℝ) ≤ |(n : ℝ)| := by
    have h1 : ((((⌈2 * a⌉₊ + 1 : ℕ) : ℤ)) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.2 hn
    rw [Int.cast_abs] at h1; simpa using h1
  have hca := Nat.le_ceil (2 * a)
  push_cast at hnR
  have hn1 : 1 ≤ |(n : ℝ)| := by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌈2 * a⌉₊)]
  have hn0 : 0 < |(n : ℝ)| := by linarith
  have hw : |(n : ℝ)| ≤ Real.sqrt (1 + (n : ℝ) ^ 2) :=
    Real.abs_le_sqrt (by nlinarith [sq_nonneg (n : ℝ)])
  have hwpos : 0 < Real.sqrt (1 + (n : ℝ) ^ 2) := by linarith
  have hδ0 : ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / |(n : ℝ)| :=
    (hxi n).trans (div_le_div_of_nonneg_left ha hn0 hw)
  have hδ : ‖(σ : ℂ) * xi n - (((σ * n : ℤ) : ℂ)) * (Real.pi : ℂ)‖ ≤ a / |(n : ℝ)| := by
    have e : (σ : ℂ) * xi n - (((σ * n : ℤ) : ℂ)) * (Real.pi : ℂ) = (σ : ℂ) * (xi n - (n : ℂ) * Real.pi) := by
      push_cast; ring
    have hs1 : ‖(σ : ℂ)‖ = 1 := by rcases hσ with rfl | rfl <;> simp
    rw [e, norm_mul, hs1, one_mul]; exact hδ0
  have hhalf : a / |(n : ℝ)| ≤ 1 / 2 := by
    rw [div_le_iff₀ hn0]; linarith
  have him : |((σ : ℂ) * xi n).im| ≤ a := by
    have h1 : |(xi n).im| ≤ a := by
      have : (xi n).im = (xi n - (n : ℂ) * Real.pi).im := by simp
      rw [this]
      exact (Complex.abs_im_le_norm _).trans (hδ0.trans (div_le_self ha hn1))
    rcases hσ with rfl | rfl <;> simpa using h1
  have hlip := NlsGge.ThirdConsultation.KSPS012Support5.Tz_lip hc1 hd ha (σ * n) him (hδ.trans hhalf)
  have hK0 : 0 ≤ K := by
    have := intervalIntegral.integral_nonneg (μ := volume) zero_le_one (fun s (_ : s ∈ Icc (0 : ℝ) 1) => norm_nonneg (d s))
    have := intervalIntegral.integral_nonneg (μ := volume) zero_le_one (fun s (_ : s ∈ Icc (0 : ℝ) 1) => norm_nonneg (c s))
    rw [hK]; positivity
  have hlip' : ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n) -
      NlsGge.ThirdConsultation.KSPS012Support5.Tz c d (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖ ≤
      K * ‖(σ : ℂ) * xi n - (((σ * n : ℤ) : ℂ)) * (Real.pi : ℂ)‖ := by rw [hK]; exact hlip
  have hb : ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n)‖ ≤
      ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖ + K * a * (1 / |(n : ℝ)|) := by
    have h1 := norm_sub_norm_le (NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n))
      (NlsGge.ThirdConsultation.KSPS012Support5.Tz c d (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ)))
    have h2 : K * ‖(σ : ℂ) * xi n - (((σ * n : ℤ) : ℂ)) * (Real.pi : ℂ)‖ ≤ K * a * (1 / |(n : ℝ)|) := by
      rw [mul_assoc, mul_one_div]; exact mul_le_mul_of_nonneg_left hδ hK0
    linarith [hlip']
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

end
end NlsGge.ThirdConsultation.KSPS017W
