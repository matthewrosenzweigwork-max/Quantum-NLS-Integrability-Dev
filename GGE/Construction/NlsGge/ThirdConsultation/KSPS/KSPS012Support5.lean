import Mathlib

                                                                                                                    
                                                                           
                                                                                    
                                                                                                                  
set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace NlsGge.ThirdConsultation.KSPS012Support5

def Tz (c d : ℝ → ℂ) (ζ : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (Complex.exp (-(2 * Complex.I * ζ * (t : ℂ))) * c t) *
    ∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s

theorem exp_lip {z z0 : ℂ} (hz0 : ‖Complex.exp z0‖ = 1) (h : ‖z - z0‖ ≤ 1) :
    ‖Complex.exp z - Complex.exp z0‖ ≤ 2 * ‖z - z0‖ := by
  have e : Complex.exp z - Complex.exp z0 = Complex.exp z0 * (Complex.exp (z - z0) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; ring_nf
  rw [e, norm_mul, hz0, one_mul]
  exact Complex.norm_exp_sub_one_le h

theorem norm_exp_mul_real_le {ζ : ℂ} {a : ℝ} (hζ : |ζ.im| ≤ a) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (sgn : ℝ) (hsgn : |sgn| ≤ 1) :
    ‖Complex.exp (sgn * (2 * Complex.I * ζ * (s : ℂ)))‖ ≤ Real.exp (2 * a) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have : ((sgn : ℂ) * (2 * Complex.I * ζ * (s : ℂ))).re = -(2 * sgn * ζ.im * s) := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  rw [this]
  have h1 : |2 * sgn * ζ.im * s| ≤ 2 * a := by
    rw [abs_mul, abs_mul, abs_mul]
    have hs' : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
    have : |(2 : ℝ)| = 2 := abs_two
    rw [this]
    have ha0 : 0 ≤ a := (abs_nonneg _).trans hζ
    calc 2 * |sgn| * |ζ.im| * |s| ≤ 2 * 1 * a * 1 := by gcongr
      _ = 2 * a := by ring
  linarith [neg_abs_le (2 * sgn * ζ.im * s), abs_nonneg (2 * sgn * ζ.im * s)]

theorem Dd_continuousOn {d : ℝ → ℂ} (hd : IntervalIntegrable d volume 0 1) (ζ : ℂ) :
    ContinuousOn (fun t : ℝ => ∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s)
      (Icc (0 : ℝ) 1) := by
  have hii : IntervalIntegrable (fun s : ℝ => Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s)
      volume 0 1 :=
    hd.continuousOn_mul (by fun_prop : Continuous fun s : ℝ =>
      Complex.exp (2 * Complex.I * ζ * (s : ℂ))).continuousOn
  have hfU : IntegrableOn (fun s : ℝ => Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s)
      (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le zero_le_one] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hii
  have := intervalIntegral.continuousOn_primitive_interval_left hfU
  rwa [uIcc_of_le zero_le_one] at this

theorem Dd_norm_le {d : ℝ → ℂ} (hd : IntervalIntegrable d volume 0 1) {ζ : ℂ} {a : ℝ}
    (hζ : |ζ.im| ≤ a) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s‖ ≤
      Real.exp (2 * a) * ∫ s in (0 : ℝ)..1, ‖d s‖ := by
  have hdn : IntervalIntegrable (fun s => ‖d s‖) volume 0 1 := hd.norm
  have h1 : ‖∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s‖ ≤
      ∫ s in t..1, Real.exp (2 * a) * ‖d s‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le ht.2 (Filter.Eventually.of_forall (fun s hs => ?_))
      ((hdn.mono_set (by
        rw [uIcc_of_le ht.2, uIcc_of_le zero_le_one]; exact Icc_subset_Icc ht.1 le_rfl)).const_mul _)
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hs.1.le, hs.2⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using norm_exp_mul_real_le hζ hs' 1 (by simp))
      (norm_nonneg _)
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
    (Filter.Eventually.of_forall (fun s => norm_nonneg _)) hdn

theorem Tz_integrable {c d : ℝ → ℂ} (hc : IntervalIntegrable c volume 0 1)
    (hd : IntervalIntegrable d volume 0 1) (ζ : ℂ) :
    IntervalIntegrable (fun t : ℝ => (Complex.exp (-(2 * Complex.I * ζ * (t : ℂ))) * c t) *
      ∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s) volume 0 1 :=
  (hc.continuousOn_mul (by fun_prop : Continuous fun t : ℝ =>
    Complex.exp (-(2 * Complex.I * ζ * (t : ℂ)))).continuousOn).mul_continuousOn
    (by rw [uIcc_of_le zero_le_one]; exact Dd_continuousOn hd ζ)

theorem norm_exp_real_axis (k : ℤ) (sgn : ℝ) (s : ℝ) :
    ‖Complex.exp ((sgn : ℂ) * (2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (s : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  have : ((sgn : ℂ) * (2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (s : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

theorem Tz_lip {c d : ℝ → ℂ} (hc : IntervalIntegrable c volume 0 1)
    (hd : IntervalIntegrable d volume 0 1) {a : ℝ} (ha : 0 ≤ a) {ζ : ℂ} (k : ℤ)
    (hζ : |ζ.im| ≤ a) (hδ : ‖ζ - (k : ℂ) * (Real.pi : ℂ)‖ ≤ 1 / 2) :
    ‖Tz c d ζ - Tz c d ((k : ℂ) * (Real.pi : ℂ))‖ ≤
      (4 * (Real.exp (2 * a) + 1) * (∫ s in (0 : ℝ)..1, ‖d s‖) * ∫ t in (0 : ℝ)..1, ‖c t‖) *
        ‖ζ - (k : ℂ) * (Real.pi : ℂ)‖ := by
  set z0 : ℂ := (k : ℂ) * (Real.pi : ℂ) with hz0
  set δ : ℂ := ζ - z0 with hδdef
  set Ld : ℝ := ∫ s in (0 : ℝ)..1, ‖d s‖ with hLd
  set Lc : ℝ := ∫ t in (0 : ℝ)..1, ‖c t‖ with hLc
  have hLd0 : 0 ≤ Ld := intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)
  have hdn : IntervalIntegrable (fun s => ‖d s‖) volume 0 1 := hd.norm
  have hz0im : |z0.im| ≤ a := by
    have : z0.im = 0 := by simp [hz0, Complex.mul_im]
    rw [this]; simpa using ha
  have hδ0 : 0 ≤ ‖δ‖ := norm_nonneg _
  -- the pointwise exponential estimates
  have hE : ∀ t ∈ Icc (0 : ℝ) 1, ‖Complex.exp (-(2 * Complex.I * ζ * (t : ℂ))) -
      Complex.exp (-(2 * Complex.I * z0 * (t : ℂ)))‖ ≤ 4 * ‖δ‖ := by
    intro t ht
    have hn : ‖-(2 * Complex.I * ζ * (t : ℂ)) - -(2 * Complex.I * z0 * (t : ℂ))‖ = 2 * ‖δ‖ * t := by
      have : -(2 * Complex.I * ζ * (t : ℂ)) - -(2 * Complex.I * z0 * (t : ℂ)) =
          -(2 * Complex.I * (t : ℂ)) * δ := by rw [hδdef]; ring
      rw [this, norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_of_nonneg ht.1]
      simp; ring
    have hz1 : ‖Complex.exp (-(2 * Complex.I * z0 * (t : ℂ)))‖ = 1 := by
      have := norm_exp_real_axis k (-1) t
      simpa [hz0, neg_mul] using this
    have hle : ‖-(2 * Complex.I * ζ * (t : ℂ)) - -(2 * Complex.I * z0 * (t : ℂ))‖ ≤ 1 := by
      rw [hn]; nlinarith [ht.1, ht.2]
    have := exp_lip hz1 hle
    rw [hn] at this
    nlinarith [ht.1, ht.2]
  have hP : ∀ s ∈ Icc (0 : ℝ) 1, ‖Complex.exp (2 * Complex.I * ζ * (s : ℂ)) -
      Complex.exp (2 * Complex.I * z0 * (s : ℂ))‖ ≤ 4 * ‖δ‖ := by
    intro s hs
    have hn : ‖2 * Complex.I * ζ * (s : ℂ) - 2 * Complex.I * z0 * (s : ℂ)‖ = 2 * ‖δ‖ * s := by
      have : 2 * Complex.I * ζ * (s : ℂ) - 2 * Complex.I * z0 * (s : ℂ) =
          (2 * Complex.I * (s : ℂ)) * δ := by rw [hδdef]; ring
      rw [this, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_of_nonneg hs.1]
      simp; ring
    have hz1 : ‖Complex.exp (2 * Complex.I * z0 * (s : ℂ))‖ = 1 := by
      have := norm_exp_real_axis k 1 s
      simpa [hz0] using this
    have hle : ‖2 * Complex.I * ζ * (s : ℂ) - 2 * Complex.I * z0 * (s : ℂ)‖ ≤ 1 := by
      rw [hn]; nlinarith [hs.1, hs.2]
    have := exp_lip hz1 hle
    rw [hn] at this
    nlinarith [hs.1, hs.2]
  -- bound on the difference of the inner integrals
  have hDd : ∀ t ∈ Icc (0 : ℝ) 1, ‖(∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s) -
      ∫ s in t..1, Complex.exp (2 * Complex.I * z0 * (s : ℂ)) * d s‖ ≤ 4 * ‖δ‖ * Ld := by
    intro t ht
    have hi : ∀ w : ℂ, IntervalIntegrable (fun s : ℝ => Complex.exp (2 * Complex.I * w * (s : ℂ)) * d s)
        volume t 1 := fun w =>
      (hd.mono_set (by rw [uIcc_of_le ht.2, uIcc_of_le zero_le_one]; exact Icc_subset_Icc ht.1 le_rfl)).continuousOn_mul
        (by fun_prop : Continuous fun s : ℝ => Complex.exp (2 * Complex.I * w * (s : ℂ))).continuousOn
    rw [← intervalIntegral.integral_sub (hi ζ) (hi z0)]
    have h1 : ‖∫ s in t..1, (Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s -
        Complex.exp (2 * Complex.I * z0 * (s : ℂ)) * d s)‖ ≤ ∫ s in t..1, 4 * ‖δ‖ * ‖d s‖ := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht.2 (Filter.Eventually.of_forall (fun s hs => ?_))
        ((hdn.mono_set (by
          rw [uIcc_of_le ht.2, uIcc_of_le zero_le_one]; exact Icc_subset_Icc ht.1 le_rfl)).const_mul _)
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hs.1.le, hs.2⟩
      rw [← sub_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hP s hs') (norm_nonneg _)
    refine h1.trans ?_
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
      (Filter.Eventually.of_forall (fun s => norm_nonneg _)) hdn
  -- assemble
  have hi1 := Tz_integrable hc hd ζ
  have hi2 := Tz_integrable hc hd z0
  unfold Tz
  rw [← intervalIntegral.integral_sub hi1 hi2]
  set K : ℝ := 4 * ‖δ‖ * (Real.exp (2 * a) + 1) * Ld with hK
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(Complex.exp (-(2 * Complex.I * ζ * (t : ℂ))) * c t) *
        (∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s) -
      (Complex.exp (-(2 * Complex.I * z0 * (t : ℂ))) * c t) *
        (∫ s in t..1, Complex.exp (2 * Complex.I * z0 * (s : ℂ)) * d s)‖ ≤ ‖c t‖ * K := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    set D1 := ∫ s in t..1, Complex.exp (2 * Complex.I * ζ * (s : ℂ)) * d s with hD1
    set D0 := ∫ s in t..1, Complex.exp (2 * Complex.I * z0 * (s : ℂ)) * d s with hD0
    set E1 := Complex.exp (-(2 * Complex.I * ζ * (t : ℂ))) with hE1
    set E0 := Complex.exp (-(2 * Complex.I * z0 * (t : ℂ))) with hE0
    have hE0n : ‖E0‖ = 1 := by
      have := norm_exp_real_axis k (-1) t
      simpa [hE0, hz0, neg_mul] using this
    have e : (E1 * c t) * D1 - (E0 * c t) * D0 = c t * ((E1 - E0) * D1 + E0 * (D1 - D0)) := by ring
    rw [e, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hE0n, one_mul]
    have h1 : ‖E1 - E0‖ ≤ 4 * ‖δ‖ := hE t ht'
    have h2 : ‖D1‖ ≤ Real.exp (2 * a) * Ld := Dd_norm_le hd hζ ht'
    have h3 : ‖D1 - D0‖ ≤ 4 * ‖δ‖ * Ld := hDd t ht'
    calc ‖E1 - E0‖ * ‖D1‖ + ‖D1 - D0‖ ≤ 4 * ‖δ‖ * (Real.exp (2 * a) * Ld) + 4 * ‖δ‖ * Ld :=
          add_le_add (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3
      _ = K := by rw [hK]; ring
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one (Filter.Eventually.of_forall hpt)
    (hc.norm.mul_const K)).trans ?_
  rw [intervalIntegral.integral_mul_const]
  refine le_of_eq ?_
  rw [hK]; ring

end NlsGge.ThirdConsultation.KSPS012Support5
