import Mathlib
import QuantumNLS.RealFourierInfra
import QuantumNLS.SineIntegralBound

/-!
# R-064239ED: the truncated Hilbert kernels `K_{a,b}(t) = 1_{a<|t|<b}/t` and their Fourier multipliers

* `Kc a b`: the kernel; `integrable_Kc` (`0 < a`), `norm_Kc_le` (`≤ 1/a`);
* **`fourier_Kc`** (Mathlib convention `𝐞(−vw) = e^{−2πivw}`): `𝓕 K_{a,b}(ξ) = −2i ∫_a^b sin(2πξt)/t dt`
  (the printed multiplier `−2i∫_ε^R sin(ξt)/t dt`, up to the `2π` of Mathlib's Fourier convention);
* `fourier_Kc_sub`: the difference of two multipliers is `−2i ∫_{a'}^{a} sin(2πξt)/t dt`, hence bounded by
  `8` and by `4π|ξ|(a − a')` (uniform absolute bound, from `SineIntegralBound`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace QuantumNLS.RootHilbert

/-- The truncated kernel `1_{a<|t|<b}/t` (complex valued). -/
def Kc (a b : ℝ) (t : ℝ) : ℂ :=
  Set.indicator {t : ℝ | a < |t| ∧ |t| < b} (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) t

theorem measurableSet_Kc (a b : ℝ) : MeasurableSet {t : ℝ | a < |t| ∧ |t| < b} :=
  have h1 : MeasurableSet {t : ℝ | a < |t|} := measurableSet_lt measurable_const continuous_abs.measurable
  have h2 : MeasurableSet {t : ℝ | |t| < b} := measurableSet_lt continuous_abs.measurable measurable_const
  h1.inter h2

theorem norm_Kc_le {a b : ℝ} (ha : 0 < a) (t : ℝ) : ‖Kc a b t‖ ≤ 1 / a := by
  unfold Kc
  by_cases h : a < |t| ∧ |t| < b
  · rw [Set.indicator_of_mem (show t ∈ {t : ℝ | a < |t| ∧ |t| < b} from h)]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, one_div]
    exact inv_anti₀ ha h.1.le
  · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | a < |t| ∧ |t| < b} from h), norm_zero]
    positivity

theorem integrable_Kc {a b : ℝ} (ha : 0 < a) : Integrable (Kc a b) (volume : Measure ℝ) := by
  have hS : {t : ℝ | a < |t| ∧ |t| < b} ⊆ Set.Icc (-b) b := fun t ht => by
    have := ht.2
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  unfold Kc
  rw [integrable_indicator_iff (measurableSet_Kc a b)]
  refine Measure.integrableOn_of_bounded (M := 1 / a) ?_ ?_ ?_
  · exact ne_of_lt (lt_of_le_of_lt (measure_mono hS) (by simp))
  · exact (Complex.measurable_ofReal.comp measurable_inv).aestronglyMeasurable
  · refine (ae_restrict_iff' (measurableSet_Kc a b)).2 (Eventually.of_forall fun t ht => ?_)
    have := norm_Kc_le (b := b) ha t
    unfold Kc at this
    rwa [Set.indicator_of_mem ht] at this

theorem cexp_real_mul_I (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) = ((Real.cos x : ℝ) : ℂ) + ((Real.sin x : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I]; simp [Complex.ofReal_cos, Complex.ofReal_sin]

/-- The integrand of the Fourier transform of `Kc` -/
def Phi (ξ : ℝ) (v : ℝ) : ℂ := Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) * ((v⁻¹ : ℝ) : ℂ)

theorem Phi_add_neg (ξ t : ℝ) :
    Phi ξ t + Phi ξ (-t) = ((-2 * (Real.sin (2 * Real.pi * ξ * t) / t) : ℝ) : ℂ) * Complex.I := by
  unfold Phi
  have e1 : (-2 * Real.pi * t * ξ : ℝ) = -(2 * Real.pi * ξ * t) := by ring
  have e2 : (-2 * Real.pi * (-t) * ξ : ℝ) = (2 * Real.pi * ξ * t) := by ring
  rw [e1, e2, cexp_real_mul_I, cexp_real_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  rw [inv_neg]
  push_cast
  ring

theorem continuous_Phi_on {ξ a b : ℝ} (hab : 0 < a) : ContinuousOn (Phi ξ) (Set.Icc a b) := by
  unfold Phi
  refine ContinuousOn.mul (by fun_prop) ?_
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  exact ContinuousOn.inv₀ continuousOn_id (fun t ht => (lt_of_lt_of_le hab ht.1).ne')

theorem continuous_Phi_neg_on {ξ a b : ℝ} (hb : b < 0) : ContinuousOn (Phi ξ) (Set.Icc a b) := by
  unfold Phi
  refine ContinuousOn.mul (by fun_prop) ?_
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  exact ContinuousOn.inv₀ continuousOn_id (fun t ht => (lt_of_le_of_lt ht.2 hb).ne)

/-- **The Fourier multiplier of the truncated kernel**:
`𝓕 K_{a,b}(ξ) = −2i ∫_a^b sin(2πξt)/t dt`. -/
theorem fourier_Kc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (ξ : ℝ) :
    𝓕 (Kc a b) ξ = ((-2 * ∫ t in a..b, Real.sin (2 * Real.pi * ξ * t) / t : ℝ) : ℂ) * Complex.I := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hS : ∀ v, Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) • Kc a b v =
      Set.indicator {t : ℝ | a < |t| ∧ |t| < b} (Phi ξ) v := by
    intro v
    unfold Kc Phi
    by_cases h : a < |v| ∧ |v| < b
    · rw [Set.indicator_of_mem (show v ∈ {t : ℝ | a < |t| ∧ |t| < b} from h),
        Set.indicator_of_mem (show v ∈ {t : ℝ | a < |t| ∧ |t| < b} from h), smul_eq_mul]
    · rw [Set.indicator_of_notMem (show v ∉ {t : ℝ | a < |t| ∧ |t| < b} from h),
        Set.indicator_of_notMem (show v ∉ {t : ℝ | a < |t| ∧ |t| < b} from h), smul_zero]
  simp only [hS]
  rw [integral_indicator (measurableSet_Kc a b)]
  have hset : {t : ℝ | a < |t| ∧ |t| < b} = Set.Ioo a b ∪ Set.Ioo (-b) (-a) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_or_gt 0 t with ht | ht
      · rw [abs_of_nonneg ht] at h1 h2; exact Or.inl ⟨h1, h2⟩
      · rw [abs_of_neg ht] at h1 h2; exact Or.inr ⟨by linarith, by linarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · rw [abs_of_pos (by linarith)]; exact ⟨h1, h2⟩
      · rw [abs_of_neg (by linarith)]; exact ⟨by linarith, by linarith⟩
  have hdisj : Disjoint (Set.Ioo a b) (Set.Ioo (-b) (-a)) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    linarith [h1.1, h2.2]
  have hint1 : IntegrableOn (Phi ξ) (Set.Ioo a b) :=
    ((continuous_Phi_on (ξ := ξ) (b := b) ha).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hint2 : IntegrableOn (Phi ξ) (Set.Ioo (-b) (-a)) :=
    ((continuous_Phi_neg_on (ξ := ξ) (a := -b) (b := -a) (by linarith)).integrableOn_Icc).mono_set
      Set.Ioo_subset_Icc_self
  rw [hset, setIntegral_union hdisj measurableSet_Ioo hint1 hint2]
  have h1 : ∫ t in Set.Ioo a b, Phi ξ t = ∫ t in a..b, Phi ξ t := by
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  have h2 : ∫ t in Set.Ioo (-b) (-a), Phi ξ t = ∫ t in a..b, Phi ξ (-t) := by
    rw [intervalIntegral.integral_comp_neg (fun t => Phi ξ t),
      intervalIntegral.integral_of_le (by linarith : -b ≤ -a), integral_Ioc_eq_integral_Ioo]
  rw [h1, h2]
  have hi1 : IntervalIntegrable (Phi ξ) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]; exact continuous_Phi_on ha
  have hi2 : IntervalIntegrable (fun t => Phi ξ (-t)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    have : ContinuousOn (Phi ξ) (Set.Icc (-b) (-a)) := continuous_Phi_neg_on (by linarith)
    exact this.comp continuous_neg.continuousOn (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  rw [← intervalIntegral.integral_add hi1 hi2]
  have : ∀ t ∈ Set.uIcc a b, Phi ξ t + Phi ξ (-t) =
      ((-2 * (Real.sin (2 * Real.pi * ξ * t) / t) : ℝ) : ℂ) * Complex.I := fun t _ => Phi_add_neg ξ t
  rw [intervalIntegral.integral_congr this, intervalIntegral.integral_mul_const]
  congr 1
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]

#print axioms fourier_Kc

/-- Multiplier bound `‖𝓕 K_{a,b}(ξ)‖ ≤ 8` (uniform in `a, b, ξ`). -/
theorem norm_fourier_Kc_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (ξ : ℝ) : ‖𝓕 (Kc a b) ξ‖ ≤ 8 := by
  rw [fourier_Kc ha hab, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul]
  have := QuantumNLS.SineIntegral.sine_integral_le_four (2 * Real.pi * ξ) ha hab
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h2]
  linarith

/-- The difference of two multipliers: `𝓕 K_{a',R} − 𝓕 K_{a,R} = −2i ∫_{a'}^{a} sin(2πξt)/t dt` for `a' ≤ a ≤ R`. -/
theorem fourier_Kc_sub {a' a R : ℝ} (ha' : 0 < a') (h1 : a' ≤ a) (h2 : a ≤ R) (ξ : ℝ) :
    𝓕 (Kc a' R) ξ - 𝓕 (Kc a R) ξ =
      ((-2 * ∫ t in a'..a, Real.sin (2 * Real.pi * ξ * t) / t : ℝ) : ℂ) * Complex.I := by
  have ha : 0 < a := lt_of_lt_of_le ha' h1
  rw [fourier_Kc ha' (h1.trans h2), fourier_Kc ha h2, ← sub_mul]
  congr 1
  have hc : ∀ x y : ℝ, 0 < x → x ≤ y →
      IntervalIntegrable (fun t : ℝ => Real.sin (2 * Real.pi * ξ * t) / t) volume x y := by
    intro x y hx hxy
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hxy]
    exact ContinuousOn.div (by fun_prop) continuousOn_id (fun t ht => (lt_of_lt_of_le hx ht.1).ne')
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hc a' a ha' h1) (hc a R ha h2)
  have hreal : -2 * (∫ t in a'..R, Real.sin (2 * Real.pi * ξ * t) / t) -
      (-2 * ∫ t in a..R, Real.sin (2 * Real.pi * ξ * t) / t) =
      -2 * ∫ t in a'..a, Real.sin (2 * Real.pi * ξ * t) / t := by
    rw [← hadd]; ring
  rw [← Complex.ofReal_sub, hreal]

/-- `‖𝓕 K_{a',R} − 𝓕 K_{a,R}‖ ≤ 2 min(4, 2π|ξ|(a − a'))`. -/
theorem norm_fourier_Kc_sub_le {a' a R : ℝ} (ha' : 0 < a') (h1 : a' ≤ a) (h2 : a ≤ R) (ξ : ℝ) :
    ‖𝓕 (Kc a' R) ξ - 𝓕 (Kc a R) ξ‖ ≤ 2 * min 4 (2 * Real.pi * |ξ| * (a - a')) := by
  rw [fourier_Kc_sub ha' h1 h2, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul]
  have h2' : |(-2 : ℝ)| = 2 := by norm_num
  rw [h2']
  have b4 := QuantumNLS.SineIntegral.sine_integral_le_four (2 * Real.pi * ξ) ha' h1
  have bl := QuantumNLS.SineIntegral.sine_integral_le_lipschitz (2 * Real.pi * ξ) ha' h1
  have hl : |2 * Real.pi * ξ| * (a - a') = 2 * Real.pi * |ξ| * (a - a') := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
  rw [hl] at bl
  have : |∫ t in a'..a, Real.sin (2 * Real.pi * ξ * t) / t| ≤ min 4 (2 * Real.pi * |ξ| * (a - a')) :=
    le_min b4 bl
  linarith

#print axioms norm_fourier_Kc_sub_le

end QuantumNLS.RootHilbert
