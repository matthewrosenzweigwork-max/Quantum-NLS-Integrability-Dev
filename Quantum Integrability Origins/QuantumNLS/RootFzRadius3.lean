import Mathlib
import QuantumNLS.RootMeasureComplex

/-!
# R-C4F43CA8 part (a), stage 3c: the `fz` estimates with `κ r ≤ 1/3`

The frozen `RootFzRadius.fz_lower_radius` and `RootMeasureComplex.fz_deriv_lower` need `κ r ≤ 1/4`. This module
gives the same two estimates for `κ r ≤ 1/3`, with constant `κ/5` in place of `κ/2`:
* `fz_deriv_lower3`: `κ/5 ≤ ‖fz'(w)‖` for `‖w‖ ≤ r`;
* `fz_lower_radius3`: `κ/5 ‖w − v‖ ≤ ‖fz w − fz v‖` for `‖w‖, ‖v‖ ≤ r`.

Numerics: for `‖x‖ ≤ 1/3`, `‖exp x − 1‖ ≤ 2‖x‖ ≤ 2/3`, `‖exp(−x)‖ ≤ e^{1/3} ≤ 3/2`, and `‖E‖ ≤ 1/16` (`HighHalf`),
so `‖exp x − 1 − E exp(−x)‖ ≤ 2/3 + 3/32 ≤ 4/5`. Standard axioms only.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Metric

namespace QuantumNLS.RootFzRadius3

open QuantumNLS.RootMeasureComplex

theorem exp_re_le_three_halves {t : ℝ} (ht : t ≤ 1 / 3) : Real.exp t ≤ 3 / 2 := by
  have h1 : -t + 1 ≤ Real.exp (-t) := Real.add_one_le_exp (-t)
  have hp : 0 < Real.exp t := Real.exp_pos t
  have h2 : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have h3 : Real.exp t * (1 - t) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hp.le]
  nlinarith [mul_le_mul_of_nonneg_left (show (2 : ℝ) / 3 ≤ 1 - t by linarith) hp.le]

theorem norm_exp_le_three_halves {x : ℂ} (hx : ‖x‖ ≤ 1 / 3) : ‖Complex.exp x‖ ≤ 3 / 2 := by
  rw [Complex.norm_exp]
  have h1 : x.re ≤ 1 / 3 := le_trans (Complex.re_le_norm x) hx
  exact exp_re_le_three_halves h1

theorem norm_Y_le {x E : ℂ} (hx : ‖x‖ ≤ 1 / 3) (hE : ‖E‖ ≤ 1 / 16) :
    ‖Complex.exp x - 1 - E * Complex.exp (-x)‖ ≤ 4 / 5 := by
  have e1 : ‖Complex.exp x - 1‖ ≤ 2 * ‖x‖ := Complex.norm_exp_sub_one_le (by linarith)
  have hneg : ‖-x‖ ≤ 1 / 3 := by
    rw [norm_neg]
    exact hx
  have e2 : ‖E * Complex.exp (-x)‖ ≤ 3 / 32 := by
    rw [norm_mul]
    have := mul_le_mul hE (norm_exp_le_three_halves hneg) (norm_nonneg _) (by norm_num)
    linarith
  have h := norm_sub_le (Complex.exp x - 1) (E * Complex.exp (-x))
  linarith

theorem one_le_norm_one_add {Y : ℂ} (hY : ‖Y‖ ≤ 4 / 5) : 1 / 5 ≤ ‖1 + Y‖ := by
  have h := norm_sub_le (1 + Y) Y
  have e : (1 + Y) - Y = 1 := by ring
  rw [e, norm_one] at h
  linarith

/-- **Derivative lower bound with `κ r ≤ 1/3`.** -/
theorem fz_deriv_lower3 {L κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {r : ℝ}
    (hr : κ * r ≤ 1 / 3) {w : ℂ} (hw : ‖w‖ ≤ r) :
    κ / 5 ≤ ‖Complex.I * κ * (Complex.exp (Complex.I * κ * w) -
      Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)))‖ := by
  have hE16 : ‖Complex.exp (Complex.I * z * L)‖ ≤ 1 / 16 := norm_exp_izL_le hz
  have hx : ‖Complex.I * κ * w‖ ≤ 1 / 3 := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ, one_mul]
    calc κ * ‖w‖ ≤ κ * r := mul_le_mul_of_nonneg_left hw hκ.le
      _ ≤ 1 / 3 := hr
  have hY := norm_Y_le hx hE16
  have hIκ : ‖Complex.I * κ‖ = κ := by
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ, one_mul]
  have hsplit : Complex.I * κ * (Complex.exp (Complex.I * κ * w) -
      Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w))) =
      Complex.I * κ * (1 + (Complex.exp (Complex.I * κ * w) - 1 -
        Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)))) := by
    ring
  rw [hsplit, norm_mul, hIκ]
  have h1 := one_le_norm_one_add hY
  calc κ / 5 = κ * (1 / 5) := by ring
    _ ≤ κ * ‖1 + (Complex.exp (Complex.I * κ * w) - 1 -
        Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)))‖ :=
      mul_le_mul_of_nonneg_left h1 hκ.le

/-- **Lipschitz lower bound with `κ r ≤ 1/3`.** -/
theorem fz_lower_radius3 {L κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {r : ℝ}
    (hr : κ * r ≤ 1 / 3) {w v : ℂ} (hw : ‖w‖ ≤ r) (hv : ‖v‖ ≤ r) :
    κ / 5 * ‖w - v‖ ≤ ‖QuantumNLS.RootMeasureComplex.fz L κ z w - QuantumNLS.RootMeasureComplex.fz L κ z v‖ := by
  have hη : 0 < z.im := by linarith [hz.1]
  set E := Complex.exp (Complex.I * z * L) with hE
  have hE16 : ‖E‖ ≤ 1 / 16 := norm_exp_izL_le hz
  let h : ℂ → ℂ := fun w => QuantumNLS.RootMeasureComplex.fz L κ z w - Complex.I * κ * w
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
    · funext x
      simp [h, QuantumNLS.RootMeasureComplex.fz, hE]
    · simp only [h']
      ring
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) r) := convex_closedBall _ _
  have hIκ : ‖Complex.I * κ‖ = κ := by
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ, one_mul]
  have hbound : ∀ y ∈ Metric.closedBall (0 : ℂ) r, ‖h' y‖ ≤ 4 / 5 * κ := by
    intro y hy
    have hy' : ‖y‖ ≤ r := by simpa using hy
    have hk : ‖Complex.I * κ * y‖ ≤ 1 / 3 := by
      rw [norm_mul, hIκ]
      calc κ * ‖y‖ ≤ κ * r := mul_le_mul_of_nonneg_left hy' hκ.le
        _ ≤ 1 / 3 := hr
    have hY := norm_Y_le hk hE16
    show ‖Complex.I * κ * (Complex.exp (Complex.I * κ * y) - 1 -
      E * Complex.exp (-(Complex.I * κ * y)))‖ ≤ 4 / 5 * κ
    rw [norm_mul, hIκ]
    calc κ * ‖Complex.exp (Complex.I * κ * y) - 1 - E * Complex.exp (-(Complex.I * κ * y))‖
        ≤ κ * (4 / 5) := mul_le_mul_of_nonneg_left hY hκ.le
      _ = 4 / 5 * κ := by ring
  have hmv := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (f := h) (f' := h') (C := 4 / 5 * κ)
    (fun y _ => (hderiv y).hasDerivWithinAt) hbound (x := v) (y := w) (by simpa using hv)
    (by simpa using hw)
  have hlin : Complex.I * κ * (w - v) =
      QuantumNLS.RootMeasureComplex.fz L κ z w - QuantumNLS.RootMeasureComplex.fz L κ z v - (h w - h v) := by
    simp only [h]
    ring
  have hn : ‖Complex.I * κ * (w - v)‖ = κ * ‖w - v‖ := by
    rw [norm_mul, hIκ]
  have h3 : κ * ‖w - v‖ ≤ ‖QuantumNLS.RootMeasureComplex.fz L κ z w - QuantumNLS.RootMeasureComplex.fz L κ z v‖ +
      ‖h w - h v‖ := by
    rw [← hn, hlin]
    exact norm_sub_le _ _
  have h4 : ‖h w - h v‖ ≤ 4 / 5 * κ * ‖w - v‖ := hmv
  nlinarith [norm_nonneg (w - v)]

end QuantumNLS.RootFzRadius3

#print axioms QuantumNLS.RootFzRadius3.fz_deriv_lower3
#print axioms QuantumNLS.RootFzRadius3.fz_lower_radius3
