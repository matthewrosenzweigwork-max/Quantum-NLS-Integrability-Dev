import NlsGge.GK38.Lib.Rouche

/-!
# Regression probes for `Rouche` (L2): `sin z` against a perturbation on `|z| = (n + 1/2)π`

* `sin` has exactly the `2n+1` simple zeros `kπ`, `|k| ≤ n`, in the disc `|z| < (n+1/2)π`.
* On the circle `|z| = (n+1/2)π`, `‖sin z‖ ≥ 1/2` (from `‖sin(x+iy)‖² = sin²x + sinh²y`).
* Hence by `rouche_circle` every `sin + ε` with `‖ε‖ < 1/2`, and more generally every analytic `g`
  with `‖g - sin‖ < 1/2` on the circle, has exactly `2n+1` zeros in the disc.  The zeros really
  move (`sin 0 + 1/4 ≠ 0`), so the statement is not vacuous.
* Hurwitz/local constancy: the count is locally constant in `ε` on the ball `‖ε‖ < 1/2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Complex Metric Set Filter Topology
open scoped Real

namespace NlsGge.GK38.Lib

noncomputable section

theorem normSq_sin' (z : ℂ) :
    Complex.normSq (Complex.sin z) = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  have h : z = (z.re : ℂ) + (z.im : ℂ) * I := (re_add_im z).symm
  rw [h, Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I, ← ofReal_sin, ← ofReal_cos,
    ← ofReal_cosh, ← ofReal_sinh]
  simp [Complex.normSq_apply, Complex.sin_ofReal_re, Complex.cos_ofReal_re,
    Complex.sinh_ofReal_re]
  nlinarith [Real.cosh_sq z.im, Real.sin_sq_add_cos_sq z.re]

theorem abs_le_abs_sinh (y : ℝ) : |y| ≤ |Real.sinh y| := by
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.2 h)]
    exact Real.self_le_sinh_iff.2 h
  · rw [abs_of_nonpos h, abs_of_nonpos (Real.sinh_nonpos_iff.2 h)]
    have := Real.self_le_sinh_iff.2 (neg_nonneg.2 h)
    rw [Real.sinh_neg] at this
    linarith

theorem cos_half_odd (n : ℕ) : Real.cos ((n + 1 / 2 : ℝ) * Real.pi) = 0 := by
  have : ((n + 1 / 2 : ℝ) * Real.pi) = Real.pi / 2 + n * Real.pi := by ring
  rw [this]
  simp [Real.cos_add_nat_mul_pi]

/-- `‖sin z‖ ≥ 1/2` on the circle `|z| = (n+1/2)π`. -/
theorem half_le_norm_sin (n : ℕ) {z : ℂ} (hz : ‖z‖ = (n + 1 / 2 : ℝ) * Real.pi) :
    1 / 2 ≤ ‖Complex.sin z‖ := by
  set r : ℝ := (n + 1 / 2 : ℝ) * Real.pi with hr
  have hpi := Real.pi_gt_three
  have hr1 : 3 / 2 < r := by
    rw [hr]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; nlinarith
  have hnorm : z.re ^ 2 + z.im ^ 2 = r ^ 2 := by
    rw [← hz, Complex.sq_norm, Complex.normSq_apply]; ring
  have hsq : 1 / 4 ≤ Complex.normSq (Complex.sin z) := by
    rw [normSq_sin']
    by_cases hy : 1 / 2 ≤ |z.im|
    · have h1 : 1 / 2 ≤ |Real.sinh z.im| := hy.trans (abs_le_abs_sinh _)
      have h2 : 1 / 4 ≤ Real.sinh z.im ^ 2 := by
        rw [← sq_abs]; nlinarith
      nlinarith [sq_nonneg (Real.sin z.re)]
    · have hy' : |z.im| < 1 / 2 := not_le.1 hy
      have hy2 : z.im ^ 2 < 1 / 4 := by
        have := sq_abs z.im
        nlinarith [abs_nonneg z.im]
      have hr0 : 0 ≤ r := by linarith
      have ha2 : |z.re| ^ 2 = r ^ 2 - z.im ^ 2 := by rw [sq_abs]; linarith
      have hale : |z.re| ≤ r := by
        by_contra hlt
        push Not at hlt
        nlinarith [abs_nonneg z.re, sq_nonneg z.im]
      set t : ℝ := r - |z.re| with ht
      have ht0 : 0 ≤ t := by rw [ht]; linarith
      have ht1 : t < 1 / 4 := by
        by_contra hge
        push Not at hge
        nlinarith [abs_nonneg z.re, sq_nonneg z.im]
      have hcos : |Real.cos z.re| ≤ t := by
        have e : Real.cos z.re = Real.sin r * Real.sin t := by
          rw [← Real.cos_abs, show |z.re| = r - t by rw [ht]; ring, Real.cos_sub,
            show r = (n + 1 / 2 : ℝ) * Real.pi from hr, cos_half_odd n]
          simp
        rw [e, abs_mul]
        calc |Real.sin r| * |Real.sin t| ≤ 1 * |Real.sin t| :=
              mul_le_mul_of_nonneg_right (Real.abs_sin_le_one r) (abs_nonneg _)
          _ ≤ |t| := by rw [one_mul]; exact Real.abs_sin_le_abs
          _ = t := abs_of_nonneg ht0
      have hc2 : Real.cos z.re ^ 2 ≤ 1 / 16 := by
        have := sq_abs (Real.cos z.re)
        nlinarith [abs_nonneg (Real.cos z.re)]
      nlinarith [Real.sin_sq_add_cos_sq z.re, sq_nonneg (Real.sinh z.im)]
  have : (1 / 2 : ℝ) ^ 2 ≤ ‖Complex.sin z‖ ^ 2 := by
    rw [Complex.sq_norm]; linarith
  exact (pow_le_pow_iff_left₀ (by norm_num) (norm_nonneg _) (by norm_num)).1 this

/-- Order of `sin` at a point: simple zeros only. -/
theorem order_sin (z : ℂ) : analyticOrderNatAt Complex.sin z = if Complex.sin z = 0 then 1 else 0 := by
  have han : AnalyticAt ℂ Complex.sin z := Complex.analyticAt_sin
  by_cases h : Complex.sin z = 0
  · rw [ite_eq_left h]
    have hcos : Complex.cos z ≠ 0 := by
      intro hc
      have := Complex.sin_sq_add_cos_sq z
      rw [h, hc] at this
      norm_num at this
    have : analyticOrderAt Complex.sin z = 1 :=
      han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h (by simpa using hcos)
    simp [analyticOrderNatAt, this]
  · rw [ite_eq_right h]
    have : analyticOrderAt Complex.sin z = 0 := han.analyticOrderAt_eq_zero.2 h
    simp [analyticOrderNatAt, this]

/-- The zeros `kπ`, `|k| ≤ n`. -/
def sinZeros (n : ℕ) : Finset ℂ := (Finset.Icc (-(n : ℤ)) n).image (fun k : ℤ => (k : ℂ) * π)

theorem card_sinZeros (n : ℕ) : (sinZeros n).card = 2 * n + 1 := by
  have hinj : Function.Injective (fun k : ℤ => (k : ℂ) * π) := by
    intro a b hab
    have : ((a : ℂ)) = b := by
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_right_cancel₀ hpi hab
    exact_mod_cast this
  rw [sinZeros, Finset.card_image_of_injective _ hinj, Int.card_Icc]
  omega

theorem mem_sinZeros {n : ℕ} {z : ℂ} :
    z ∈ sinZeros n ↔ Complex.sin z = 0 ∧ ‖z‖ < (n + 1 / 2 : ℝ) * Real.pi := by
  constructor
  · intro hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    refine ⟨Complex.sin_eq_zero_iff.2 ⟨k, rfl⟩, ?_⟩
    have : ‖((k : ℂ) * π)‖ = |(k : ℝ)| * Real.pi := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      simp
    rw [this]
    refine mul_lt_mul_of_pos_right ?_ Real.pi_pos
    rw [abs_lt]
    constructor <;> [skip; skip] <;>
      · have h1 : (-(n : ℝ)) ≤ k := by exact_mod_cast hk1
        have h2 : (k : ℝ) ≤ n := by exact_mod_cast hk2
        linarith
  · rintro ⟨hz, hn⟩
    obtain ⟨k, rfl⟩ := Complex.sin_eq_zero_iff.1 hz
    refine Finset.mem_image.2 ⟨k, Finset.mem_Icc.2 ?_, rfl⟩
    have : ‖((k : ℂ) * π)‖ = |(k : ℝ)| * Real.pi := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      simp
    rw [this] at hn
    have h3 : |(k : ℝ)| < n + 1 / 2 := lt_of_mul_lt_mul_right hn Real.pi_pos.le
    rw [abs_lt] at h3
    constructor
    · have : (-(n : ℝ)) - 1 / 2 < k := by linarith [h3.1]
      have : (-(n : ℤ)) - 1 < k := by exact_mod_cast (by linarith : (-(n : ℝ)) - 1 < k)
      omega
    · have : (k : ℝ) < n + 1 := by linarith [h3.2]
      have : k < (n : ℤ) + 1 := by exact_mod_cast this
      omega

/-- The zeros of `sin` in `|z| < (n+1/2)π`: `kπ` for `|k| ≤ n`, each simple. -/
theorem zeroMultiset_sin (n : ℕ) :
    zeroMultiset Complex.sin (ball 0 ((n + 1 / 2 : ℝ) * Real.pi)) = (sinZeros n).val := by
  classical
  refine Multiset.ext' fun z => ?_
  rw [count_zeroMultiset_ball (fun w _ => Complex.analyticAt_sin), order_sin]
  by_cases hz : z ∈ sinZeros n
  · rw [Multiset.count_eq_one_of_mem (sinZeros n).nodup hz]
    obtain ⟨h1, h2⟩ := mem_sinZeros.1 hz
    rw [ite_eq_left (by simpa [mem_ball, dist_zero_right] using h2), ite_eq_left h1]
  · rw [Multiset.count_eq_zero_of_notMem (by simpa using hz)]
    by_cases hb : z ∈ ball (0 : ℂ) ((n + 1 / 2 : ℝ) * Real.pi)
    · rw [ite_eq_left hb, ite_eq_right]
      intro h1
      exact hz (mem_sinZeros.2 ⟨h1, by simpa [mem_ball, dist_zero_right] using hb⟩)
    · rw [ite_eq_right hb]

theorem card_zeroMultiset_sin (n : ℕ) :
    Multiset.card (zeroMultiset Complex.sin (ball 0 ((n + 1 / 2 : ℝ) * Real.pi))) = 2 * n + 1 := by
  rw [zeroMultiset_sin]
  exact card_sinZeros n

/-- **Probe.**  Any analytic `g` within `1/2` of `sin` on the circle `|z| = (n+1/2)π` has exactly
`2n+1` zeros inside. -/
theorem probe_rouche_sin (n : ℕ) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 ((n + 1 / 2 : ℝ) * Real.pi)))
    (h : ∀ z ∈ sphere (0 : ℂ) ((n + 1 / 2 : ℝ) * Real.pi), ‖g z - Complex.sin z‖ < 1 / 2) :
    Multiset.card (zeroMultiset g (ball 0 ((n + 1 / 2 : ℝ) * Real.pi))) = 2 * n + 1 := by
  have hR : 0 < (n + 1 / 2 : ℝ) * Real.pi := by positivity
  rw [← card_zeroMultiset_sin n]
  refine rouche_circle hR (fun z _ => Complex.analyticAt_sin) hg fun z hz => ?_
  have hz' : ‖z‖ = (n + 1 / 2 : ℝ) * Real.pi := by
    simpa [mem_sphere, dist_zero_right] using hz
  exact (h z hz).trans_le (half_le_norm_sin n hz')

/-- **Probe (constant perturbation).**  `sin z + ε` with `‖ε‖ < 1/2` has `2n+1` zeros in
`|z| < (n+1/2)π`. -/
theorem probe_rouche_sin_add_const (n : ℕ) {ε : ℂ} (hε : ‖ε‖ < 1 / 2) :
    Multiset.card (zeroMultiset (fun z => Complex.sin z + ε)
      (ball 0 ((n + 1 / 2 : ℝ) * Real.pi))) = 2 * n + 1 :=
  probe_rouche_sin n (fun z _ => Complex.analyticAt_sin.add analyticAt_const)
    (fun z _ => by simpa using hε)

/-- The perturbation really moves the zeros (so the previous probe is not a tautology): `0` is a
zero of `sin` but not of `sin + 1/4`. -/
theorem probe_rouche_nonvacuous :
    Complex.sin 0 = 0 ∧ (Complex.sin 0 + 1 / 4 : ℂ) ≠ 0 := by
  simp

/-- **Probe (local constancy in the parameter).**  The zero count of `sin z + ε` on the circle is
locally constant on the open ball `‖ε‖ < 1/2` (`zeroCount_locallyConstant` in a non-trivial
parameter space). -/
theorem probe_locallyConstant_sin (n : ℕ) :
    IsLocallyConstant fun ε : {ε : ℂ // ‖ε‖ < 1 / 2} =>
      Multiset.card (zeroMultiset (fun z => Complex.sin z + ε.1)
        (ball 0 ((n + 1 / 2 : ℝ) * Real.pi))) := by
  have hR : 0 < (n + 1 / 2 : ℝ) * Real.pi := by positivity
  refine zeroCount_locallyConstant (F := fun (ε : {ε : ℂ // ‖ε‖ < 1 / 2}) z => Complex.sin z + ε.1)
    hR (fun ε z _ => Complex.analyticAt_sin.add analyticAt_const) ?_ ?_
  · refine Continuous.continuousOn ?_
    exact (Complex.continuous_sin.comp continuous_snd).add
      (continuous_subtype_val.comp continuous_fst)
  · intro ε z hz
    have hz' : ‖z‖ = (n + 1 / 2 : ℝ) * Real.pi := by
      simpa [mem_sphere, dist_zero_right] using hz
    have h1 := half_le_norm_sin n hz'
    intro h0
    have : Complex.sin z = -ε.1 := by linear_combination h0
    have h2 : ‖Complex.sin z‖ < 1 / 2 := by rw [this, norm_neg]; exact ε.2
    linarith

/-- **Probe (Hurwitz along a sequence).**  `sin z + 1/(k+4) → sin z` uniformly on the circle, and
the zero counts agree eventually (here in fact for all `k`). -/
theorem probe_hurwitz_sin (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, Multiset.card (zeroMultiset (fun z => Complex.sin z + 1 / ((k : ℂ) + 4))
      (ball 0 ((n + 1 / 2 : ℝ) * Real.pi))) =
      Multiset.card (zeroMultiset Complex.sin (ball 0 ((n + 1 / 2 : ℝ) * Real.pi))) := by
  have hR : 0 < (n + 1 / 2 : ℝ) * Real.pi := by positivity
  refine hurwitz_circle atTop hR (Eventually.of_forall fun k z _ =>
    Complex.analyticAt_sin.add analyticAt_const) (fun z _ => Complex.analyticAt_sin)
    (fun z hz => ?_) ?_
  · intro h0
    have hz' : ‖z‖ = (n + 1 / 2 : ℝ) * Real.pi := by
      simpa [mem_sphere, dist_zero_right] using hz
    have := half_le_norm_sin n hz'
    rw [h0, norm_zero] at this
    linarith
  · refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
    filter_upwards [eventually_ge_atTop K] with k hk z _
    rw [dist_eq_norm]
    have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < (k : ℝ) + 4 := by positivity
    have : ‖Complex.sin z - (Complex.sin z + 1 / ((k : ℂ) + 4))‖ = 1 / ((k : ℝ) + 4) := by
      rw [show Complex.sin z - (Complex.sin z + 1 / ((k : ℂ) + 4)) = -(1 / ((k : ℂ) + 4)) by ring,
        norm_neg, norm_div, norm_one]
      congr 1
      have : (k : ℂ) + 4 = (((k : ℝ) + 4 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg hkpos.le]
    rw [this, div_lt_iff₀ hkpos]
    rw [div_lt_iff₀ hε] at hK
    nlinarith

end

end NlsGge.GK38.Lib
