import QuantumNLS.ClassicalCharges

/-!
# Charge energy preparation: real `I_2`, Fourier kinetic form, `H¹`-extension of `I_3`

Builds on the frozen `ClassicalCharges` (DEF-022, sha256 ca5e1365…) and the frozen Fourier /
WeakDerivatives modules (f0c07d6f…, 030e4611…).  Proved here (no dynamics, no conservation law,
no Poisson bracket assumed):

* `charge_two_conj`, `charge_two_real`: `I_2 = ∫ ū(−i u')` is real, `I_2 = ∫₀^L Im(ū u')`
  (integration by parts / FTC for `(|u|²)'` on the circle).
* `coeff_deriv`, `hasSum_kinetic`: `û'(n) = (2πin/L) û(n)` and the exact Fourier kinetic form
  `∫₀^L |u'|² = Σ_n (2πn/L)² |û(n)|²` for smooth periodic `u` (Parseval).
* `kinetic`, `quartic`, `energyH1`: `E_κ = K + κ Q` on `H¹(𝕋_L)` (F04 `H04 L 1` fields), with
  `K(f) = Σ (2πn/L)²|f̂(n)|²`, `Q(f) = ∫|f|⁴`; well defined on `L²`-classes (`energyH1_congr_ae`).
* `hasSum_quartic`: exact Fourier convolution form
  `Q(f) = Σ_n |L^{-1/2} Σ_k f̂(k) f̂(n−k)|²` from `h04_mul` and `coeff_mul_seriesRep`.
* `kinetic_sub_le`, `quartic_sub_le`, `energyH1_sub_le`: explicit local Lipschitz estimates in the
  F04 `H¹` norm (kinetic by weighted Cauchy–Schwarz; quartic from the `L¹`–sup embedding
  `h04_l1_sup`), `energyH1_continuous` (ε–δ) and `energyH1_tendsto` (sequential).
* `charge_three_eq_energyH1`: on smooth periodic `u`, `I_3^{(κ)}(u) = E_κ(ũ)` — the extension is
  an extension of the DEF-022 charge.
-/

open scoped ComplexConjugate ContDiff
open MeasureTheory QuantumNLS.Fourier QuantumNLS.WeakDerivatives QuantumNLS.ClassicalCharges

noncomputable section

namespace QuantumNLS.ChargeEnergy

variable {L : ℝ}

/-! ## Part 1: `I_2` is real -/

theorem deriv_continuous {u : ℝ → ℂ} (hu : SmoothPeriodic L u) : Continuous (deriv u) :=
  (contDiff_infty_iff_deriv.mp hu.smooth).2.continuous

theorem hasDerivAt_of_smooth {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (x : ℝ) :
    HasDerivAt u (deriv u x) x :=
  ((contDiff_infty_iff_deriv.mp hu.smooth).1 x).hasDerivAt

theorem intervalIntegral_conj {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 L) :
    ∫ x in (0 : ℝ)..L, conj (f x) = conj (∫ x in (0 : ℝ)..L, f x) := by
  have := ContinuousLinearMap.intervalIntegral_comp_comm
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap hf
  simpa using this

/-- `∫₀^L (ū u' + u ū') = 0`: the circle integral of `(|u|²)'`. -/
theorem integral_conj_mul_deriv_add {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    ∫ x in (0 : ℝ)..L, (conj (u x) * deriv u x + u x * conj (deriv u x)) = 0 := by
  have h1 := hasDerivAt_of_smooth hu
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) L, HasDerivAt (fun y => conj (u y) * u y)
      (conj (u x) * deriv u x + u x * conj (deriv u x)) x := by
    intro x _
    have := ((h1 x).star).mul (h1 x)
    refine this.congr_deriv ?_
    simp only [Complex.star_def]; ring
  have hc : Continuous (fun x => conj (u x) * deriv u x + u x * conj (deriv u x)) :=
    ((Complex.continuous_conj.comp hu.smooth.continuous).mul (deriv_continuous hu)).add
      (hu.smooth.continuous.mul (Complex.continuous_conj.comp (deriv_continuous hu)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  have e1 : u L = u 0 := by simpa using hu.periodic 0
  simp only [e1]; ring

/-- **`I_2` is real.**  `conj I_2 = I_2`. -/
theorem charge_two_conj (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    conj (charge L κ u 2) = charge L κ u 2 := by
  have hc1 := deriv_continuous hu
  have hcu := hu.smooth.continuous
  have hA : IntervalIntegrable (fun x => conj (u x) * deriv u x) volume 0 L :=
    ((Complex.continuous_conj.comp hcu).mul hc1).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun x => u x * conj (deriv u x)) volume 0 L :=
    (hcu.mul (Complex.continuous_conj.comp hc1)).intervalIntegrable _ _
  have hsum := integral_conj_mul_deriv_add hu
  rw [intervalIntegral.integral_add hA hB] at hsum
  have hI : IntervalIntegrable (fun x => conj (u x) * (-Complex.I * deriv u x)) volume 0 L :=
    ((Complex.continuous_conj.comp hcu).mul (continuous_const.mul hc1)).intervalIntegrable _ _
  rw [charge_two, ← intervalIntegral_conj hI]
  have e1 : ∫ x in (0 : ℝ)..L, conj (u x) * (-Complex.I * deriv u x)
      = -Complex.I * ∫ x in (0 : ℝ)..L, conj (u x) * deriv u x := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  have e2 : ∫ x in (0 : ℝ)..L, conj (conj (u x) * (-Complex.I * deriv u x))
      = Complex.I * ∫ x in (0 : ℝ)..L, u x * conj (deriv u x) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x
    simp only [map_mul, map_neg, Complex.conj_conj, Complex.conj_I]; ring
  rw [e2, e1]
  linear_combination Complex.I * hsum

/-- The real value of `I_2`: `I_2 = ∫₀^L Im(ū u')` (`(−i z).re = z.im`). -/
theorem charge_two_real (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    charge L κ u 2 = ((∫ x in (0 : ℝ)..L, (conj (u x) * deriv u x).im : ℝ) : ℂ) := by
  have hc1 := deriv_continuous hu
  have hcu := hu.smooth.continuous
  have hA : Continuous (fun x => conj (u x) * deriv u x) :=
    (Complex.continuous_conj.comp hcu).mul hc1
  have hreal : (charge L κ u 2).im = 0 := by
    have := congrArg Complex.im (charge_two_conj κ hu)
    simp only [Complex.conj_im] at this
    linarith
  have e1 : charge L κ u 2 = -Complex.I * ∫ x in (0 : ℝ)..L, conj (u x) * deriv u x := by
    rw [charge_two, ← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  apply Complex.ext
  · rw [Complex.ofReal_re, e1]
    have : (∫ x in (0 : ℝ)..L, conj (u x) * deriv u x).im
        = ∫ x in (0 : ℝ)..L, (conj (u x) * deriv u x).im := by
      rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _
        (hA.intervalIntegrable _ _)]
      rfl
    simp [this]
  · rw [Complex.ofReal_im]; exact hreal

/-! ## Part 2: exact Fourier kinetic form for smooth profiles -/

section Kinetic

variable [Fact (0 < L)]

/-- Integration by parts against the mode `χ_n`: `∫ χ_n u' = (2πin/L) ∫ χ_n u`. -/
theorem integral_chi_mul_deriv {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (n : ℤ) :
    ∫ x in (0 : ℝ)..L, chi L n x * deriv u x = ikn L n * ∫ x in (0 : ℝ)..L, chi L n x * u x := by
  have hchi : ∀ x, HasDerivAt (chi L n) (-(ikn L n) * chi L n x) x := hasDerivAt_chi n
  have hcc : Continuous (chi L n) := (chi_isTest (L := L) n).smooth.continuous
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := L)
    (u := chi L n) (u' := fun x => -(ikn L n) * chi L n x) (v := u) (v' := deriv u)
    (fun x _ => hchi x) (fun x _ => hasDerivAt_of_smooth hu x)
    ((continuous_const.mul hcc).intervalIntegrable _ _)
    ((deriv_continuous hu).intervalIntegrable _ _)
  have hb : chi L n L * u L - chi L n 0 * u 0 = 0 := by
    have e1 : u L = u 0 := by simpa using hu.periodic 0
    have e2 : chi L n L = chi L n 0 := by simpa using (chi_isTest (L := L) n).periodic 0
    rw [e1, e2]; ring
  rw [key, hb, zero_sub, ← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_neg]
  congr 1; funext x; ring

/-- The Fourier coefficients of `u'` are `(2πin/L) û(n)`. -/
theorem coeff_deriv {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (n : ℤ) :
    coeff L (liftC (deriv_continuous hu) (periodic_deriv hu.periodic) : AddCircle L → ℂ) n =
      ikn L n * coeff L (liftC hu.smooth.continuous hu.periodic : AddCircle L → ℂ) n := by
  rw [coeff_eq_interval, coeff_eq_interval]
  have e1 : ∫ x in (0 : ℝ)..L, chi L n x *
      (liftC (deriv_continuous hu) (periodic_deriv hu.periodic) : AddCircle L → ℂ) x
      = ∫ x in (0 : ℝ)..L, chi L n x * deriv u x := by
    congr 1
  have e2 : ∫ x in (0 : ℝ)..L, chi L n x *
      (liftC hu.smooth.continuous hu.periodic : AddCircle L → ℂ) x
      = ∫ x in (0 : ℝ)..L, chi L n x * u x := by
    congr 1
  rw [e1, e2, integral_chi_mul_deriv hu]; ring

/-- **Exact Fourier kinetic form.**  For a smooth periodic `u`,
`∫₀^L |u'|² = Σ_n (2πn/L)² |û(n)|²` (Parseval for `u'` with `û'(n) = (2πin/L) û(n)`). -/
theorem hasSum_kinetic {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    HasSum (fun n : ℤ => freq L n ^ 2 *
        ‖coeff L (liftC hu.smooth.continuous hu.periodic : AddCircle L → ℂ) n‖ ^ 2)
      (∫ x in (0 : ℝ)..L, ‖deriv u x‖ ^ 2) := by
  set G := liftC (deriv_continuous hu) (periodic_deriv hu.periodic) with hG
  have h := hasSum_sq_coeff (L := L) (memLp_of_continuous G.continuous)
  have e : ∫ x in (0 : ℝ)..L, ‖deriv u x‖ ^ 2 = ∫ t, ‖G t‖ ^ 2 ∂(volume : Measure (AddCircle L)) := by
    have := AddCircle.intervalIntegral_preimage L 0 (fun a : AddCircle L => ‖G a‖ ^ 2)
    rw [zero_add] at this
    rw [← this]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [hG, liftC_coe]
  rw [e]
  convert h using 2 with n
  rw [show coeff L (G : AddCircle L → ℂ) n = _ from coeff_deriv hu n, norm_ikn_mul_sq]

end Kinetic

/-! ## Part 3a: weighted `ℓ²` estimates for the kinetic term (sequence level) -/

section Seq

set_option linter.unusedSectionVars false

variable [Fact (0 < L)]

theorem weight_sq (n : ℤ) : Real.sqrt (1 + freq L n ^ 2) ^ 2 = 1 + freq L n ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Triangle inequality for the F04 `H¹` weight: if `‖c_n‖ ≤ ‖a_n‖ + ‖b_n‖` then
`c ∈ h¹` and `‖c‖ ≤ ‖a‖ + ‖b‖` (Minkowski, from `sqrt_tsum_add_le`). -/
theorem mem04_le_add {c a b : ℤ → ℂ} (ha : Mem04 L 1 a) (hb : Mem04 L 1 b)
    (h : ∀ n, ‖c n‖ ≤ ‖a n‖ + ‖b n‖) :
    Mem04 L 1 c ∧ Real.sqrt (f04NormSq L 1 c) ≤
      Real.sqrt (f04NormSq L 1 a) + Real.sqrt (f04NormSq L 1 b) := by
  set F : ℤ → ℝ := fun n => Real.sqrt (1 + freq L n ^ 2) * ‖a n‖ with hF
  set G : ℤ → ℝ := fun n => Real.sqrt (1 + freq L n ^ 2) * ‖b n‖ with hG
  have hF2 : ∀ n, F n ^ 2 = f04Weight L 1 n * ‖a n‖ ^ 2 := fun n => by
    simp only [hF, mul_pow, weight_sq, f04Weight_one]
  have hG2 : ∀ n, G n ^ 2 = f04Weight L 1 n * ‖b n‖ ^ 2 := fun n => by
    simp only [hG, mul_pow, weight_sq, f04Weight_one]
  have hF0 : ∀ n, 0 ≤ F n := fun n => by simp only [hF]; positivity
  have hG0 : ∀ n, 0 ≤ G n := fun n => by simp only [hG]; positivity
  have hFs : Summable fun n => F n ^ 2 := by simp_rw [hF2]; exact ha
  have hGs : Summable fun n => G n ^ 2 := by simp_rw [hG2]; exact hb
  obtain ⟨hsum, hmink⟩ := sqrt_tsum_add_le hF0 hG0 hFs hGs
  have hpt : ∀ n, f04Weight L 1 n * ‖c n‖ ^ 2 ≤ (F n + G n) ^ 2 := fun n => by
    have hw : 0 ≤ Real.sqrt (1 + freq L n ^ 2) := Real.sqrt_nonneg _
    have : Real.sqrt (1 + freq L n ^ 2) * ‖c n‖ ≤ F n + G n := by
      simp only [hF, hG]; rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (h n) hw
    calc f04Weight L 1 n * ‖c n‖ ^ 2 = (Real.sqrt (1 + freq L n ^ 2) * ‖c n‖) ^ 2 := by
          rw [mul_pow, weight_sq, f04Weight_one]
      _ ≤ (F n + G n) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
  have hc : Mem04 L 1 c :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (f04Weight_pos L 1 n).le (by positivity)) hpt hsum
  refine ⟨hc, ?_⟩
  have hle : f04NormSq L 1 c ≤ ∑' n, (F n + G n) ^ 2 := hc.tsum_le_tsum hpt hsum
  simp_rw [hF2, hG2] at hmink
  exact (Real.sqrt_le_sqrt hle).trans hmink

/-- `(Σ p_n²|a_n|²)` is summable for `a ∈ h¹`. -/
theorem kin_summable {a : ℤ → ℂ} (ha : Mem04 L 1 a) :
    Summable fun n : ℤ => (|freq L n| * ‖a n‖) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ha
  rw [mul_pow, sq_abs, f04Weight_one]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem kin_eq (a : ℤ → ℂ) : (fun n : ℤ => (|freq L n| * ‖a n‖) ^ 2) =
    fun n : ℤ => freq L n ^ 2 * ‖a n‖ ^ 2 := funext fun n => by rw [mul_pow, sq_abs]

theorem kin_le_norm {a : ℤ → ℂ} (ha : Mem04 L 1 a) :
    ∑' n : ℤ, freq L n ^ 2 * ‖a n‖ ^ 2 ≤ f04NormSq L 1 a := by
  have hs := kin_summable ha
  rw [kin_eq] at hs
  unfold f04NormSq
  refine hs.tsum_le_tsum (fun n => ?_) ha
  rw [f04Weight_one]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **Kinetic Lipschitz estimate (sequence level).**
`|Σ p²|a|² − Σ p²|b|²| ≤ (‖a‖ + ‖b‖) ‖a − b‖` in the F04 `H¹` norm. -/
theorem kin_diff_le {a b : ℤ → ℂ} (ha : Mem04 L 1 a) (hb : Mem04 L 1 b) :
    |(∑' n : ℤ, freq L n ^ 2 * ‖a n‖ ^ 2) - ∑' n : ℤ, freq L n ^ 2 * ‖b n‖ ^ 2| ≤
      (Real.sqrt (f04NormSq L 1 a) + Real.sqrt (f04NormSq L 1 b)) *
        Real.sqrt (f04NormSq L 1 (fun n => a n - b n)) := by
  obtain ⟨hab, -⟩ := mem04_le_add (c := fun n => a n - b n) ha hb
    (fun n => by simpa [sub_eq_add_neg] using norm_sub_le (a n) (b n))
  set x : ℤ → ℝ := fun n => |freq L n| * ‖a n‖ with hx
  set y : ℤ → ℝ := fun n => |freq L n| * ‖b n‖ with hy
  set z : ℤ → ℝ := fun n => |freq L n| * ‖a n - b n‖ with hz
  have hx0 : ∀ n, 0 ≤ x n := fun n => by positivity
  have hy0 : ∀ n, 0 ≤ y n := fun n => by positivity
  have hz0 : ∀ n, 0 ≤ z n := fun n => by positivity
  have hxs : Summable fun n => x n ^ 2 := kin_summable ha
  have hys : Summable fun n => y n ^ 2 := kin_summable hb
  have hzs : Summable fun n => z n ^ 2 := kin_summable hab
  obtain ⟨hxz, cs1⟩ := tsum_mul_sq_le hx0 hz0 hxs hzs
  obtain ⟨hyz, cs2⟩ := tsum_mul_sq_le hy0 hz0 hys hzs
  have hXn : 0 ≤ ∑' n, x n ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have hYn : 0 ≤ ∑' n, y n ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have hZn : 0 ≤ ∑' n, z n ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have h1 : ∑' n, x n * z n ≤ Real.sqrt (∑' n, x n ^ 2) * Real.sqrt (∑' n, z n ^ 2) := by
    rw [← Real.sqrt_mul hXn]; exact Real.le_sqrt_of_sq_le cs1
  have h2 : ∑' n, y n * z n ≤ Real.sqrt (∑' n, y n ^ 2) * Real.sqrt (∑' n, z n ^ 2) := by
    rw [← Real.sqrt_mul hYn]; exact Real.le_sqrt_of_sq_le cs2
  -- pointwise
  have hpt : ∀ n, |x n ^ 2 - y n ^ 2| ≤ x n * z n + y n * z n := fun n => by
    have hxy : |x n - y n| ≤ z n := by
      simp only [hx, hy, hz]
      rw [← mul_sub, abs_mul, abs_abs]
      exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (abs_nonneg _)
    calc |x n ^ 2 - y n ^ 2| = |x n - y n| * (x n + y n) := by
          rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (hx0 n) (hy0 n))]; ring
      _ ≤ z n * (x n + y n) :=
          mul_le_mul_of_nonneg_right hxy (add_nonneg (hx0 n) (hy0 n))
      _ = _ := by ring
  have hsumd : Summable fun n => |x n ^ 2 - y n ^ 2| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpt (hxz.add hyz)
  have hxe : ∀ n, x n ^ 2 = freq L n ^ 2 * ‖a n‖ ^ 2 := fun n => by simp only [hx, mul_pow, sq_abs]
  have hye : ∀ n, y n ^ 2 = freq L n ^ 2 * ‖b n‖ ^ 2 := fun n => by simp only [hy, mul_pow, sq_abs]
  have hze : ∀ n, z n ^ 2 = freq L n ^ 2 * ‖a n - b n‖ ^ 2 := fun n => by
    simp only [hz, mul_pow, sq_abs]
  have hdiff : (∑' n : ℤ, freq L n ^ 2 * ‖a n‖ ^ 2) - ∑' n : ℤ, freq L n ^ 2 * ‖b n‖ ^ 2 =
      ∑' n, (x n ^ 2 - y n ^ 2) := by
    rw [hxs.tsum_sub hys]
    simp only [hxe, hye]
  have hX : ∑' n, x n ^ 2 ≤ f04NormSq L 1 a := by
    simp_rw [hxe]; exact kin_le_norm ha
  have hY : ∑' n, y n ^ 2 ≤ f04NormSq L 1 b := by
    simp_rw [hye]; exact kin_le_norm hb
  have hZ : ∑' n, z n ^ 2 ≤ f04NormSq L 1 (fun n => a n - b n) := by
    simp_rw [hze]; exact kin_le_norm hab
  rw [hdiff]
  calc |∑' n, (x n ^ 2 - y n ^ 2)| = ‖∑' n, (x n ^ 2 - y n ^ 2)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖x n ^ 2 - y n ^ 2‖ := norm_tsum_le_tsum_norm (by simpa using hsumd)
    _ ≤ ∑' n, (x n * z n + y n * z n) :=
        (by simpa using hsumd : Summable fun n => ‖x n ^ 2 - y n ^ 2‖).tsum_le_tsum
          (fun n => by simpa using hpt n) (hxz.add hyz)
    _ = ∑' n, x n * z n + ∑' n, y n * z n := hxz.tsum_add hyz
    _ ≤ Real.sqrt (∑' n, x n ^ 2) * Real.sqrt (∑' n, z n ^ 2) +
          Real.sqrt (∑' n, y n ^ 2) * Real.sqrt (∑' n, z n ^ 2) := add_le_add h1 h2
    _ ≤ (Real.sqrt (f04NormSq L 1 a) + Real.sqrt (f04NormSq L 1 b)) *
          Real.sqrt (f04NormSq L 1 (fun n => a n - b n)) := by
        rw [← add_mul]
        have hs1 := Real.sqrt_le_sqrt hX
        have hs2 := Real.sqrt_le_sqrt hY
        have hs3 := Real.sqrt_le_sqrt hZ
        exact mul_le_mul (add_le_add hs1 hs2) hs3 (Real.sqrt_nonneg _)
          (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end Seq

/-! ## Part 3b: the energy functional on `H¹(𝕋_L)` (function level) -/

section H1

set_option linter.unusedSectionVars false

variable [Fact (0 < L)]

/-- The Fourier kinetic form `K(f) = Σ_n (2πn/L)² |f̂(n)|²`. -/
def kinetic (f : AddCircle L → ℂ) : ℝ := ∑' n : ℤ, freq L n ^ 2 * ‖coeff L f n‖ ^ 2

/-- The quartic form `Q(f) = ∫_{𝕋_L} |f|⁴` (mass-`L` measure). -/
def quartic (f : AddCircle L → ℂ) : ℝ := ∫ x, ‖f x‖ ^ 4 ∂(volume : Measure (AddCircle L))

/-- The extended energy `E_κ(f) = K(f) + κ Q(f)` on `H¹`. -/
def energyH1 (κ : ℝ) (f : AddCircle L → ℂ) : ℝ := kinetic f + κ * quartic f

theorem h04Norm_nonneg' (f : AddCircle L → ℂ) : 0 ≤ h04Norm L 1 f := Real.sqrt_nonneg _

/-- The difference of two `H¹` fields is `H¹`, with coefficients `â − b̂`. -/
theorem h04_sub {f g : AddCircle L → ℂ} (hf : H04 L 1 f) (hg : H04 L 1 g) :
    H04 L 1 (fun x => f x - g x) ∧
      coeff L (fun x => f x - g x) = fun n => coeff L f n - coeff L g n := by
  have hco : coeff L (fun x => f x - g x) = fun n => coeff L f n - coeff L g n :=
    funext fun n => coeff_sub_integrable (integrable_of_h04 hf.1) (integrable_of_h04 hg.1) n
  refine ⟨⟨hf.1.sub hg.1, ?_⟩, hco⟩
  rw [hco]
  exact (mem04_le_add (c := fun n => coeff L f n - coeff L g n) hf.2 hg.2
    (fun n => by simpa [sub_eq_add_neg] using norm_sub_le (coeff L f n) (coeff L g n))).1

/-- Triangle inequality in the `H¹` norm for differences. -/
theorem h04Norm_le_add_sub {f g : AddCircle L → ℂ} (hf : H04 L 1 f) (hg : H04 L 1 g) :
    h04Norm L 1 g ≤ h04Norm L 1 f + h04Norm L 1 (fun x => f x - g x) := by
  obtain ⟨hd, hco⟩ := h04_sub hf hg
  have := (mem04_le_add (c := coeff L g) hf.2 hd.2 (fun n => by
    have h := norm_sub_le (coeff L f n) (coeff L f n - coeff L g n)
    simp only [sub_sub_cancel] at h
    rw [congrFun hco n]
    exact h)).2
  exact this

/-- **Kinetic part is Lipschitz on `H¹`**: `|K(f) − K(g)| ≤ (‖f‖_{H¹} + ‖g‖_{H¹}) ‖f − g‖_{H¹}`. -/
theorem kinetic_sub_le {f g : AddCircle L → ℂ} (hf : H04 L 1 f) (hg : H04 L 1 g) :
    |kinetic f - kinetic g| ≤
      (h04Norm L 1 f + h04Norm L 1 g) * h04Norm L 1 (fun x => f x - g x) := by
  obtain ⟨hd, hco⟩ := h04_sub hf hg
  have := kin_diff_le hf.2 hg.2
  unfold kinetic h04Norm
  rw [hco]
  exact this

/-- A.e. sup bound `‖f(x)‖ ≤ c_L ‖f‖_{H¹}` (reuse of `h04_l1_sup`). -/
theorem ae_norm_le {f : AddCircle L → ℂ} (hf : H04 L 1 f) :
    ∀ᵐ x ∂(volume : Measure (AddCircle L)), ‖f x‖ ≤ cL L * h04Norm L 1 f := by
  obtain ⟨-, -, g, -, hae, hb⟩ := h04_l1_sup hf
  filter_upwards [hae] with x hx
  rw [hx]; exact hb x

theorem quartic_integrable {f : AddCircle L → ℂ} (hf : H04 L 1 f) :
    Integrable (fun x => ‖f x‖ ^ 4) (volume : Measure (AddCircle L)) := by
  refine Integrable.of_bound (C := (cL L * h04Norm L 1 f) ^ 4) ?_ ?_
  · exact (hf.1.aestronglyMeasurable.norm.aemeasurable.pow_const 4).aestronglyMeasurable
  · filter_upwards [ae_norm_le hf] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 4

/-- **Quartic part is locally Lipschitz on `H¹`** (the actual quartic estimate, from the
`L¹`–sup embedding): with `m_f = c_L‖f‖`, `|Q(f) − Q(g)| ≤ L c_L⁴ (‖f‖+‖g‖)(‖f‖²+‖g‖²) ‖f − g‖`. -/
theorem quartic_sub_le {f g : AddCircle L → ℂ} (hf : H04 L 1 f) (hg : H04 L 1 g) :
    |quartic f - quartic g| ≤
      L * cL L ^ 4 * ((h04Norm L 1 f + h04Norm L 1 g) *
        (h04Norm L 1 f ^ 2 + h04Norm L 1 g ^ 2)) * h04Norm L 1 (fun x => f x - g x) := by
  have hL : 0 < L := Fact.out
  obtain ⟨hd, -⟩ := h04_sub hf hg
  have h1 := ae_norm_le hf
  have h2 := ae_norm_le hg
  have h3 := ae_norm_le hd
  set mf := cL L * h04Norm L 1 f
  set mg := cL L * h04Norm L 1 g
  set md := cL L * h04Norm L 1 (fun x => f x - g x)
  have hbound : ∀ᵐ x ∂(volume : Measure (AddCircle L)),
      ‖‖f x‖ ^ 4 - ‖g x‖ ^ 4‖ ≤ md * ((mf + mg) * (mf ^ 2 + mg ^ 2)) := by
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    have A := norm_nonneg (f x)
    have B := norm_nonneg (g x)
    have hdiff : |‖f x‖ - ‖g x‖| ≤ ‖f x - g x‖ := abs_norm_sub_norm_le _ _
    have e : ‖f x‖ ^ 4 - ‖g x‖ ^ 4 = (‖f x‖ - ‖g x‖) * ((‖f x‖ + ‖g x‖) * (‖f x‖ ^ 2 + ‖g x‖ ^ 2)) := by
      ring
    rw [Real.norm_eq_abs, e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (‖f x‖ + ‖g x‖) * (‖f x‖ ^ 2 + ‖g x‖ ^ 2))]
    have hmd : 0 ≤ md := by
      have := norm_nonneg (f x - g x); linarith
    refine mul_le_mul (hdiff.trans hx3) ?_ (by positivity) hmd
    exact mul_le_mul (add_le_add hx1 hx2)
      (add_le_add (pow_le_pow_left₀ A hx1 2) (pow_le_pow_left₀ B hx2 2)) (by positivity)
      (by linarith [A.trans hx1, B.trans hx2])
  unfold quartic
  rw [← integral_sub (quartic_integrable hf) (quartic_integrable hg), ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const hbound).trans ?_
  rw [measureReal_def, torus_mass, ENNReal.toReal_ofReal hL.le]
  simp only [md, mf, mg]
  nlinarith [cL]

end H1

/-! ## Part 3c: a.e.-invariance, exact Fourier quartic form, continuity -/

section H1b

set_option linter.unusedSectionVars false

variable [Fact (0 < L)]

/-- The energy functional is well defined on `L²`-classes. -/
theorem energyH1_congr_ae (κ : ℝ) {f g : AddCircle L → ℂ}
    (h : f =ᵐ[(volume : Measure (AddCircle L))] g) : energyH1 κ f = energyH1 κ g := by
  have hk : kinetic f = kinetic g := by
    unfold kinetic; exact tsum_congr fun n => by rw [coeff_congr_ae L h n]
  have hq : quartic f = quartic g := by
    unfold quartic
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx; rw [hx]
  unfold energyH1; rw [hk, hq]

/-- **Exact Fourier (convolution) form of the quartic term.**  For `f ∈ H¹`,
`∫ |f|⁴ = ‖f²‖₂² = Σ_n | L^{-1/2} Σ_k f̂(k) f̂(n−k) |²`, via the Fourier product lemma
`coeff_mul_seriesRep` and `h04_mul` (no quartic identity is assumed). -/
theorem hasSum_quartic {f : AddCircle L → ℂ} (hf : H04 L 1 f) :
    HasSum (fun n : ℤ => ‖(((Real.sqrt L)⁻¹ : ℝ) : ℂ) * ∑' k : ℤ, coeff L f k * coeff L f (n - k)‖ ^ 2)
      (quartic f) := by
  obtain ⟨hmul, -⟩ := h04_mul hf hf
  have haf := ae_eq_seriesRep hf.1 hf.2
  have hS := summable_norm_of_mem04 le_rfl hf.2
  have hae : (fun x => f x * f x) =ᵐ[(volume : Measure (AddCircle L))]
      fun x => seriesRep L (coeff L f) x * seriesRep L (coeff L f) x := by
    filter_upwards [haf] with x hx; rw [hx]
  have h := hasSum_sq_coeff (L := L) hmul.1
  have hq : quartic f = ∫ t, ‖f t * f t‖ ^ 2 ∂(volume : Measure (AddCircle L)) := by
    unfold quartic
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul]; ring
  rw [hq]
  convert h using 2 with n
  rw [coeff_congr_ae L hae n, coeff_mul_seriesRep hS hS n]

/-- **Explicit local Lipschitz bound for the extended energy on `H¹`.** -/
theorem energyH1_sub_le (κ : ℝ) {f g : AddCircle L → ℂ} (hf : H04 L 1 f) (hg : H04 L 1 g) :
    |energyH1 κ f - energyH1 κ g| ≤
      ((h04Norm L 1 f + h04Norm L 1 g) +
        |κ| * (L * cL L ^ 4 * ((h04Norm L 1 f + h04Norm L 1 g) *
          (h04Norm L 1 f ^ 2 + h04Norm L 1 g ^ 2)))) * h04Norm L 1 (fun x => f x - g x) := by
  have hk := kinetic_sub_le hf hg
  have hq := quartic_sub_le hf hg
  have e : energyH1 κ f - energyH1 κ g = (kinetic f - kinetic g) + κ * (quartic f - quartic g) := by
    unfold energyH1; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have := mul_le_mul_of_nonneg_left hq (abs_nonneg κ)
  nlinarith [this, hk]

/-- **Continuity of the extended energy in the `H¹` norm** (ε–δ form with the explicit `H¹`
distance `‖f − g‖_{H¹}`).  The extension of `I_3` is therefore continuous on `H¹`. -/
theorem energyH1_continuous (κ : ℝ) {f : AddCircle L → ℂ} (hf : H04 L 1 f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : AddCircle L → ℂ, H04 L 1 g →
      h04Norm L 1 (fun x => f x - g x) < δ → |energyH1 κ f - energyH1 κ g| < ε := by
  have hL : 0 < L := Fact.out
  set N := h04Norm L 1 f with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  set C : ℝ := ((N + (N + 1)) + |κ| * (L * cL L ^ 4 * ((N + (N + 1)) * (N ^ 2 + (N + 1) ^ 2)))) with hC
  have hc0 : 0 ≤ cL L := Real.sqrt_nonneg _
  have hC0 : 0 ≤ C := by positivity
  refine ⟨min 1 (ε / (C + 1)), lt_min one_pos (div_pos hε (by linarith)), fun g hg hd => ?_⟩
  have hd1 : h04Norm L 1 (fun x => f x - g x) < 1 := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : h04Norm L 1 (fun x => f x - g x) < ε / (C + 1) := lt_of_lt_of_le hd (min_le_right _ _)
  have hNg : h04Norm L 1 g ≤ N + 1 := by
    have := h04Norm_le_add_sub hf hg; linarith
  have hNg0 : 0 ≤ h04Norm L 1 g := Real.sqrt_nonneg _
  have hmono : ((N + h04Norm L 1 g) +
        |κ| * (L * cL L ^ 4 * ((N + h04Norm L 1 g) * (N ^ 2 + h04Norm L 1 g ^ 2)))) ≤ C := by
    have h1 : N + h04Norm L 1 g ≤ N + (N + 1) := by linarith
    have h2 : N ^ 2 + h04Norm L 1 g ^ 2 ≤ N ^ 2 + (N + 1) ^ 2 := by
      have := pow_le_pow_left₀ hNg0 hNg 2; linarith
    have h3 : (N + h04Norm L 1 g) * (N ^ 2 + h04Norm L 1 g ^ 2) ≤
        (N + (N + 1)) * (N ^ 2 + (N + 1) ^ 2) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : L * cL L ^ 4 * ((N + h04Norm L 1 g) * (N ^ 2 + h04Norm L 1 g ^ 2)) ≤
        L * cL L ^ 4 * ((N + (N + 1)) * (N ^ 2 + (N + 1) ^ 2)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 := mul_le_mul_of_nonneg_left h4 (abs_nonneg κ)
    simp only [hC]; linarith
  have hb := energyH1_sub_le κ hf hg
  have hdn : 0 ≤ h04Norm L 1 (fun x => f x - g x) := Real.sqrt_nonneg _
  calc |energyH1 κ f - energyH1 κ g| ≤ C * h04Norm L 1 (fun x => f x - g x) :=
        hb.trans (mul_le_mul_of_nonneg_right hmono hdn)
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hd2.le hC0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith

/-- **Sequential continuity**: `f_k → f` in `H¹` implies `E_κ(f_k) → E_κ(f)`. -/
theorem energyH1_tendsto (κ : ℝ) {f : AddCircle L → ℂ} (hf : H04 L 1 f)
    {fk : ℕ → AddCircle L → ℂ} (hfk : ∀ k, H04 L 1 (fk k))
    (hlim : Filter.Tendsto (fun k => h04Norm L 1 (fun x => f x - fk k x)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => energyH1 κ (fk k)) Filter.atTop (nhds (energyH1 κ f)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := energyH1_continuous κ hf hε
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hlim) δ hδ
  refine ⟨K, fun k hk => ?_⟩
  have hk' := hK k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (h04Norm_nonneg' _)] at hk'
  rw [Real.dist_eq, abs_sub_comm]
  exact h (fk k) (hfk k) hk'

end H1b

/-! ## Part 4: agreement with the DEF-022 charge `I_3` on smooth profiles -/

section Agree

set_option linter.unusedSectionVars false

variable [Fact (0 < L)]

/-- A smooth periodic profile, lifted to `𝕋_L`, is an `H¹` field (F04). -/
theorem smooth_h04 {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    H04 L 1 (liftC hu.smooth.continuous hu.periodic : AddCircle L → ℂ) := by
  set F := liftC hu.smooth.continuous hu.periodic with hF
  have hml := memLp_of_continuous (L := L) F.continuous
  refine ⟨hml, ?_⟩
  have h1 := (hasSum_sq_coeff (L := L) hml).summable
  have h2 := (hasSum_kinetic hu).summable
  have := h1.add h2
  unfold Mem04
  refine this.congr (fun n => ?_)
  rw [f04Weight_one]; ring

/-- The kinetic form of a smooth profile is `∫₀^L |u'|²`. -/
theorem kinetic_smooth {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    kinetic (liftC hu.smooth.continuous hu.periodic : AddCircle L → ℂ) =
      ∫ x in (0 : ℝ)..L, ‖deriv u x‖ ^ 2 :=
  (hasSum_kinetic hu).tsum_eq

/-- The quartic form of a smooth profile is `∫₀^L |u|⁴`. -/
theorem quartic_smooth {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    quartic (liftC hu.smooth.continuous hu.periodic : AddCircle L → ℂ) =
      ∫ x in (0 : ℝ)..L, ‖u x‖ ^ 4 := by
  unfold quartic
  have := AddCircle.intervalIntegral_preimage L 0
    (fun a : AddCircle L => ‖(liftC hu.smooth.continuous hu.periodic : AddCircle L → ℂ) a‖ ^ 4)
  rw [zero_add] at this
  rw [← this]
  exact intervalIntegral.integral_congr (fun x _ => by simp only [liftC_coe])

/-- **The `H¹` extension agrees with the classical `I_3`** on smooth periodic profiles:
`I_3^{(κ)}(u) = E_κ(ũ)` (as a complex number, in particular `I_3` is real). -/
theorem charge_three_eq_energyH1 (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    charge L κ u 3 =
      ((energyH1 κ (liftC hu.smooth.continuous hu.periodic : AddCircle L → ℂ) : ℝ) : ℂ) := by
  rw [charge_three L κ hu]
  congr 1
  unfold energyH1
  have hi1 : IntervalIntegrable (fun x => ‖deriv u x‖ ^ 2) volume 0 L :=
    ((continuous_norm.comp (deriv_continuous hu)).pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => κ * ‖u x‖ ^ 4) volume 0 L :=
    (continuous_const.mul ((continuous_norm.comp hu.smooth.continuous).pow 4)).intervalIntegrable _ _
  rw [kinetic_smooth hu, quartic_smooth hu, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul]

end Agree

#print axioms charge_two_conj
#print axioms charge_two_real
#print axioms coeff_deriv
#print axioms hasSum_kinetic
#print axioms kinetic_sub_le
#print axioms quartic_sub_le
#print axioms energyH1_congr_ae
#print axioms hasSum_quartic
#print axioms energyH1_sub_le
#print axioms energyH1_continuous
#print axioms energyH1_tendsto
#print axioms smooth_h04
#print axioms kinetic_smooth
#print axioms quartic_smooth
#print axioms charge_three_eq_energyH1

end QuantumNLS.ChargeEnergy
