import QuantumNLS.RootMeasureComplex

/-!
# R-C4F43CA8 part (3)(ii)-a: the lower bound `fz` on a general disk

`fz_lower` (RootMeasureComplex, frozen) states `κ/2 ‖w − v‖ ≤ ‖fz w − fz v‖` on the disk of radius `(Im z)⁻¹`.
Part (3) needs the same bound on the disk of radius `r = ‖u‖²/Im z`, `u` near the unit sphere (the radius
of `mass_characterization`). The proof of `fz_lower` is reproduced with the radius replaced by `r`, under the
hypothesis `κ r ≤ 1/4` (which holds for `r = ‖u‖²/Im z` when `4κ‖u‖² ≤ Im z`, i.e. `HighHalf L (κ‖u‖²) z`).
Realized inputs (frozen): `RootMeasureComplex.HighHalf`, `fz`, `norm_exp_izL_le`, `norm_exp_sub_one_le'`,
`norm_exp_le_four_thirds`.

Proved here (standard axioms only): `fz_lower_radius` (the bound on the disk of radius `r`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology Metric

namespace QuantumNLS.RootFzRadius

open QuantumNLS.RootMeasureComplex

theorem fz_lower_radius {L κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {r : ℝ}
    (hr : κ * r ≤ 1 / 4) {w v : ℂ} (hw : ‖w‖ ≤ r) (hv : ‖v‖ ≤ r) :
    κ / 2 * ‖w - v‖ ≤ ‖fz L κ z w - fz L κ z v‖ := by
  have hη : 0 < z.im := by linarith [hz.1]
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
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) r) := convex_closedBall _ _
  have hbound : ∀ y ∈ Metric.closedBall (0 : ℂ) r, ‖h' y‖ ≤ 5 * κ / 12 := by
    intro y hy
    have hy' : ‖y‖ ≤ r := by simpa using hy
    have hk : ‖Complex.I * κ * y‖ ≤ 1 / 4 := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ,
        one_mul]
      calc κ * ‖y‖ ≤ κ * r := mul_le_mul_of_nonneg_left hy' hκ.le
        _ ≤ 1 / 4 := hr
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



end QuantumNLS.RootFzRadius

#print axioms QuantumNLS.RootFzRadius.fz_lower_radius
