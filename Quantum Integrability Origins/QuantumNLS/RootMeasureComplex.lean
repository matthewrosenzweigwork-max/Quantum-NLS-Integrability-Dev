import Mathlib

/-!
# R-09E1EAE9 `thm:root-measure`, Steps 1 and 2: the uniformly injective scalar map and the deterministic product error

Source: `source/chapters/foundations/ROOT_spectral_measure.tex`, proof of `thm:root-measure` (line 105), Steps 1-2.
Pure complex analysis (no EXT-025 contract is needed here).

* **Step 1.**  `f_z(w) = e^{iκw} + e^{izL} e^{-iκw}`.  For `η = Im z ≥ η₀ = max{4κ, L⁻¹ log 16}` and `|w|,|v| ≤ η⁻¹`,
  `|f_z(w) − f_z(v)| ≥ (κ/2)|w − v|` (`fz_lower`, `eq:root-inverse-bound`).  Proof as printed: subtract the constant derivative
  `iκ` before estimating (`|f_z'(w) − iκ| ≤ 5κ/12 < κ/2`, here via the mean value inequality on the disk).
* **Step 2.**  For `t_j = iκ/(N(z − q_j))` (`|t_j| ≤ x/N ≤ 1/4`, `x = κ/η`), `|s_N(z) − f_z(G_N(z))| ≤ 3x²/N`
  (`eq:root-product-error`, absolute `C₀ = 3`), where `s_N(z) = ∏(1 + t_j) + e^{izL}∏(1 − t_j)` and `G_N(z) = N⁻¹∑(z − q_j)⁻¹`
  (`product_error`).  No rapidity moment is used.
-/

set_option autoImplicit false

open Complex

noncomputable section

namespace QuantumNLS.RootMeasureComplex

/-- `f_z(w) = e^{iκw} + e^{izL}e^{-iκw}`. -/
def fz (L κ : ℝ) (z w : ℂ) : ℂ :=
  Complex.exp (Complex.I * κ * w) + Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w))

/-- The high half-plane `Im z ≥ η₀ = max{4κ, L⁻¹ log 16}`. -/
def HighHalf (L κ : ℝ) (z : ℂ) : Prop := 4 * κ ≤ z.im ∧ Real.log 16 ≤ L * z.im

theorem exp_quarter_le : Real.exp (1 / 4) ≤ 4 / 3 := by
  have h1 : (3 / 4 : ℝ) ≤ Real.exp (-(1 / 4)) := by
    have := Real.add_one_le_exp (-(1 / 4 : ℝ)); linarith
  have h2 : Real.exp (1 / 4) * Real.exp (-(1 / 4)) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (1 / 4), Real.exp_pos (-(1 / 4 : ℝ))]

theorem norm_exp_le_four_thirds {x : ℂ} (hx : ‖x‖ ≤ 1 / 4) : ‖Complex.exp x‖ ≤ 4 / 3 := by
  rw [Complex.norm_exp]
  refine (Real.exp_le_exp.2 ((Complex.re_le_norm x).trans hx)).trans exp_quarter_le

theorem norm_exp_sub_one_le' {x : ℂ} (hx : ‖x‖ ≤ 1 / 4) : ‖Complex.exp x - 1‖ ≤ 4 / 3 * ‖x‖ := by
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) (1 / 4)) := convex_closedBall _ _
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Complex.exp) (f' := Complex.exp)
    (C := 4 / 3) (fun y _ => (Complex.hasDerivAt_exp y).hasDerivWithinAt)
    (fun y hy => norm_exp_le_four_thirds (by simpa using hy))
    (x := 0) (y := x) (by simp) (by simpa using hx)
  simpa using h

theorem norm_exp_izL_le {L κ : ℝ} {z : ℂ} (hz : HighHalf L κ z) :
    ‖Complex.exp (Complex.I * z * L)‖ ≤ 1 / 16 := by
  rw [Complex.norm_exp]
  have : (Complex.I * z * (L : ℂ)).re = -(L * z.im) := by simp [Complex.mul_re]; ring
  rw [this]
  have h16 : Real.exp (-Real.log 16) = 1 / 16 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  calc Real.exp (-(L * z.im)) ≤ Real.exp (-Real.log 16) := Real.exp_le_exp.2 (by linarith [hz.2])
    _ = 1 / 16 := h16

/-- **Step 1** (`eq:root-inverse-bound`). -/
theorem fz_lower {L κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {w v : ℂ}
    (hw : ‖w‖ ≤ (z.im)⁻¹) (hv : ‖v‖ ≤ (z.im)⁻¹) :
    κ / 2 * ‖w - v‖ ≤ ‖fz L κ z w - fz L κ z v‖ := by
  have hη : 0 < z.im := by linarith [hz.1]
  have hx : κ * (z.im)⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hη]; linarith [hz.1]
  set E := Complex.exp (Complex.I * z * L) with hE
  have hE16 : ‖E‖ ≤ 1 / 16 := norm_exp_izL_le hz
  -- h(w) = f(w) - iκ w
  let h : ℂ → ℂ := fun w => fz L κ z w - Complex.I * κ * w
  let h' : ℂ → ℂ := fun w => Complex.I * κ *
    (Complex.exp (Complex.I * κ * w) - 1 - E * Complex.exp (-(Complex.I * κ * w)))
  have hderiv : ∀ w, HasDerivAt h (h' w) w := by
    intro w
    have h1 : HasDerivAt (fun w : ℂ => Complex.I * κ * w) (Complex.I * κ) w := by
      simpa using (hasDerivAt_id w).const_mul (Complex.I * κ)
    have h2 : HasDerivAt (fun w : ℂ => Complex.exp (Complex.I * κ * w))
        (Complex.exp (Complex.I * κ * w) * (Complex.I * κ)) w := h1.cexp
    have h3 : HasDerivAt (fun w : ℂ => Complex.exp (-(Complex.I * κ * w)))
        (Complex.exp (-(Complex.I * κ * w)) * (-(Complex.I * κ))) w := h1.neg.cexp
    have h4 := (h2.add (h3.const_mul E)).sub h1
    convert h4 using 1
    · funext x; simp [h, fz, hE]
    · simp only [h']; ring
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) ((z.im)⁻¹)) := convex_closedBall _ _
  have hbound : ∀ y ∈ Metric.closedBall (0 : ℂ) ((z.im)⁻¹), ‖h' y‖ ≤ 5 * κ / 12 := by
    intro y hy
    have hy' : ‖y‖ ≤ (z.im)⁻¹ := by simpa using hy
    have hk : ‖Complex.I * κ * y‖ ≤ 1 / 4 := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ,
        one_mul]
      calc κ * ‖y‖ ≤ κ * (z.im)⁻¹ := mul_le_mul_of_nonneg_left hy' hκ.le
        _ ≤ 1 / 4 := hx
    have e1 := norm_exp_sub_one_le' hk
    have e2 : ‖Complex.exp (-(Complex.I * κ * y))‖ ≤ 4 / 3 :=
      norm_exp_le_four_thirds (by simpa using hk)
    have hky : ‖Complex.I * κ * y‖ = κ * ‖y‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ,
        one_mul]
    have hky4 : κ * ‖y‖ ≤ 1 / 4 := hky ▸ hk
    show ‖Complex.I * κ * (Complex.exp (Complex.I * κ * y) - 1 -
      E * Complex.exp (-(Complex.I * κ * y)))‖ ≤ 5 * κ / 12
    rw [norm_mul, Complex.norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hκ, one_mul]
    have h5 : ‖Complex.exp (Complex.I * κ * y) - 1 - E * Complex.exp (-(Complex.I * κ * y))‖ ≤
        5 / 12 := by
      calc _ ≤ ‖Complex.exp (Complex.I * κ * y) - 1‖ + ‖E * Complex.exp (-(Complex.I * κ * y))‖ := by
            have := norm_sub_le (Complex.exp (Complex.I * κ * y) - 1) (E * Complex.exp (-(Complex.I * κ * y)))
            exact this
        _ ≤ 4 / 3 * (κ * ‖y‖) + 1 / 16 * (4 / 3) := by
            gcongr
            · rw [← hky]; exact e1
            · rw [norm_mul]; exact mul_le_mul hE16 e2 (norm_nonneg _) (by norm_num)
        _ ≤ 4 / 3 * (1 / 4) + 1 / 16 * (4 / 3) := by gcongr
        _ = 5 / 12 := by norm_num
    nlinarith [h5, hκ]
  have hmv := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (f := h) (f' := h') (C := 5 * κ / 12)
    (fun y _ => (hderiv y).hasDerivWithinAt) hbound (x := v) (y := w) (by simpa using hv)
    (by simpa using hw)
  have hlin : Complex.I * κ * (w - v) = fz L κ z w - fz L κ z v - (h w - h v) := by
    simp only [h]; ring
  have hn : ‖Complex.I * κ * (w - v)‖ = κ * ‖w - v‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ,
      one_mul]
  have h3 : κ * ‖w - v‖ ≤ ‖fz L κ z w - fz L κ z v‖ + ‖h w - h v‖ := by
    rw [← hn, hlin]
    exact norm_sub_le _ _
  have h4 : ‖h w - h v‖ ≤ 5 * κ / 12 * ‖w - v‖ := hmv
  nlinarith [norm_nonneg (w - v)]


/-! ### Step 2: the deterministic product error -/

section Product

theorem prod_exp_error {n : ℕ} (hn : 0 < n) (t : Fin n → ℂ) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4)
    (ht : ∀ j, ‖t j‖ ≤ x / n) :
    ‖(∏ j, (1 + t j)) - Complex.exp (∑ j, t j)‖ ≤ 2 * x ^ 2 / n := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have ht4 : ∀ j, ‖t j‖ ≤ 1 / 4 := fun j =>
    (ht j).trans ((div_le_self hx0 hnr).trans hx)
  have hne : ∀ j, (1 + t j) ≠ 0 := by
    intro j h
    have : ‖t j‖ = 1 := by
      have : t j = -1 := by linear_combination h
      rw [this]; simp
    linarith [ht4 j]
  set δ : ℂ := ∑ j, (Complex.log (1 + t j) - t j) with hδ
  have hδb : ‖δ‖ ≤ 2 / 3 * x ^ 2 / n := by
    calc ‖δ‖ ≤ ∑ j, ‖Complex.log (1 + t j) - t j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, (2 / 3) * (x / n) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 := Complex.norm_log_one_add_sub_self_le (z := t j) (by linarith [ht4 j])
          have h2 : (1 - ‖t j‖)⁻¹ ≤ 4 / 3 := by
            rw [inv_le_comm₀ (by linarith [ht4 j]) (by norm_num)]; linarith [ht4 j]
          have h3 : ‖t j‖ ^ 2 ≤ (x / n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (ht j) 2
          have h2' : 0 ≤ (1 - ‖t j‖)⁻¹ := inv_nonneg.2 (by linarith [ht4 j])
          have h4 := mul_le_mul h3 h2 h2' (sq_nonneg _)
          calc _ ≤ ‖t j‖ ^ 2 * (1 - ‖t j‖)⁻¹ / 2 := h1
            _ ≤ (x / n) ^ 2 * (4 / 3) / 2 := by linarith
            _ = 2 / 3 * (x / n) ^ 2 := by ring
      _ = 2 / 3 * x ^ 2 / n := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hprod : (∏ j, (1 + t j)) = Complex.exp (∑ j, t j) * Complex.exp δ := by
    rw [← Complex.exp_add, hδ, Finset.sum_sub_distrib]
    rw [show (∑ j, t j) + (∑ j, Complex.log (1 + t j) - ∑ j, t j) = ∑ j, Complex.log (1 + t j) by ring,
      Complex.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Complex.exp_log (hne j)).symm
  have hS : ‖∑ j, t j‖ ≤ 1 / 4 := by
    calc ‖∑ j, t j‖ ≤ ∑ j, ‖t j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, x / n := Finset.sum_le_sum fun j _ => ht j
      _ = x := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
      _ ≤ 1 / 4 := hx
  have hδ4 : ‖δ‖ ≤ 1 / 4 := by
    have : 2 / 3 * x ^ 2 / n ≤ 1 / 4 := by
      have hx2 : x ^ 2 ≤ 1 / 16 := by nlinarith
      calc 2 / 3 * x ^ 2 / n ≤ 2 / 3 * x ^ 2 / 1 := by
            apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hnr
        _ ≤ 1 / 4 := by nlinarith
    exact hδb.trans this
  rw [hprod]
  calc ‖Complex.exp (∑ j, t j) * Complex.exp δ - Complex.exp (∑ j, t j)‖
      = ‖Complex.exp (∑ j, t j)‖ * ‖Complex.exp δ - 1‖ := by
        rw [← norm_mul]; congr 1; ring
    _ ≤ 4 / 3 * (4 / 3 * (2 / 3 * x ^ 2 / n)) := by
        apply mul_le_mul (norm_exp_le_four_thirds hS) _ (norm_nonneg _) (by norm_num)
        exact (norm_exp_sub_one_le' hδ4).trans (by gcongr)
    _ ≤ 2 * x ^ 2 / n := by
        have : 0 ≤ x ^ 2 / n := by positivity
        have e : 4 / 3 * (4 / 3 * (2 / 3 * x ^ 2 / n)) = (32 / 27) * (x ^ 2 / n) := by ring
        rw [e]; have : 2 * x ^ 2 / n = 2 * (x ^ 2 / n) := by ring
        rw [this]; nlinarith

/-- `s_N(z) = ∏(1 + iκ/(N(z−q_j))) + e^{izL}∏(1 − iκ/(N(z−q_j)))` (the on-shell eigenvalue of `S_N(z)`). -/
def sProd (L κ : ℝ) (N : ℕ) (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  (∏ j, (1 + Complex.I * κ / (N * (z - q j)))) +
    Complex.exp (Complex.I * z * L) * ∏ j, (1 - Complex.I * κ / (N * (z - q j)))

/-- `G_N(z) = N⁻¹ ∑_j (z − q_j)⁻¹`, the Cauchy transform of `N⁻¹∑δ_{q_j}`. -/
def GN (N : ℕ) (q : Fin N → ℝ) (z : ℂ) : ℂ := (N : ℂ)⁻¹ * ∑ j, (z - q j)⁻¹

/-- **Step 2** (`eq:root-product-error`): for `Im z = η ≥ η₀`, `x = κ/η`, `|s_N(z) − f_z(G_N(z))| ≤ 3x²/N`. -/
theorem product_error {L κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {N : ℕ} (hN : 0 < N)
    (q : Fin N → ℝ) :
    ‖sProd L κ N q z - fz L κ z (GN N q z)‖ ≤ 3 * (κ / z.im) ^ 2 / N := by
  have hη : 0 < z.im := by linarith [hz.1]
  have hx0 : 0 ≤ κ / z.im := by positivity
  have hx : κ / z.im ≤ 1 / 4 := by rw [div_le_iff₀ hη]; linarith [hz.1]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set t : Fin N → ℂ := fun j => Complex.I * κ / (N * (z - q j)) with ht
  have htb : ∀ j, ‖t j‖ ≤ (κ / z.im) / N := by
    intro j
    have hzq : z.im ≤ ‖z - (q j : ℂ)‖ := by
      have := Complex.abs_im_le_norm (z - (q j : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      exact (le_abs_self _).trans this
    have hpos : 0 < ‖z - (q j : ℂ)‖ := lt_of_lt_of_le hη hzq
    simp only [ht]
    rw [norm_div, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ,
      one_mul, norm_mul, Complex.norm_natCast]
    rw [div_div]
    exact div_le_div_of_nonneg_left hκ.le (by positivity) (by nlinarith [hzq, hNr])
  have hsum : ∑ j, t j = Complex.I * κ * GN N q z := by
    unfold GN
    simp only [ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  have e1 := prod_exp_error hN t hx0 hx htb
  have e2 := prod_exp_error hN (fun j => -t j) hx0 hx (fun j => by simpa using htb j)
  have hE := norm_exp_izL_le hz
  have h1 : ‖(∏ j, (1 + t j)) - Complex.exp (Complex.I * κ * GN N q z)‖ ≤ 2 * (κ / z.im) ^ 2 / N := by
    rw [← hsum]; exact e1
  have h2 : ‖(∏ j, (1 - t j)) - Complex.exp (-(Complex.I * κ * GN N q z))‖ ≤
      2 * (κ / z.im) ^ 2 / N := by
    have e2' := e2
    rw [Finset.sum_neg_distrib, hsum] at e2'
    simpa only [← sub_eq_add_neg] using e2'
  unfold sProd fz
  have hdiff : (∏ j, (1 + Complex.I * κ / (N * (z - q j)))) +
      Complex.exp (Complex.I * z * L) * (∏ j, (1 - Complex.I * κ / (N * (z - q j)))) -
      (Complex.exp (Complex.I * κ * GN N q z) +
        Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * GN N q z))) =
      ((∏ j, (1 + t j)) - Complex.exp (Complex.I * κ * GN N q z)) +
        Complex.exp (Complex.I * z * L) *
          ((∏ j, (1 - t j)) - Complex.exp (-(Complex.I * κ * GN N q z))) := by
    simp only [ht]; ring
  rw [hdiff]
  calc _ ≤ ‖(∏ j, (1 + t j)) - Complex.exp (Complex.I * κ * GN N q z)‖ +
        ‖Complex.exp (Complex.I * z * L)‖ *
          ‖(∏ j, (1 - t j)) - Complex.exp (-(Complex.I * κ * GN N q z))‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ 2 * (κ / z.im) ^ 2 / N + 1 / 16 * (2 * (κ / z.im) ^ 2 / N) := by gcongr
    _ ≤ 3 * (κ / z.im) ^ 2 / N := by
        have : 0 ≤ (κ / z.im) ^ 2 / N := by positivity
        have e : 2 * (κ / z.im) ^ 2 / N + 1 / 16 * (2 * (κ / z.im) ^ 2 / N) = (17 / 8) * ((κ / z.im) ^ 2 / N) := by ring
        rw [e, show 3 * (κ / z.im) ^ 2 / N = 3 * ((κ / z.im) ^ 2 / N) by ring]
        nlinarith

end Product

end QuantumNLS.RootMeasureComplex

#print axioms QuantumNLS.RootMeasureComplex.fz_lower
#print axioms QuantumNLS.RootMeasureComplex.prod_exp_error
#print axioms QuantumNLS.RootMeasureComplex.product_error
