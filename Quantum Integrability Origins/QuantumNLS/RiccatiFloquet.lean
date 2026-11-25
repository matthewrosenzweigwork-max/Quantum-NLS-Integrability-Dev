import Mathlib

/-!
# E5 Floquet algebra (R-3FEAD88B, prop:riccati)

Pure algebraic core of the Floquet/log-branch step, with no ODE content:

1. `trace_exp_identity`: with `m = exp(-izL/2 + κJ)`,
   `exp(izL/2) (m + m⁻¹) = exp(κJ) (1 + w)` where `w = exp(izL - 2κJ)`.
2. `trace_eq_of_det_one_eigen`: a 2x2 matrix of determinant 1 with eigenvalue `m`
   has trace `m + m⁻¹`.
3. `tail_exp_bound`, `log_tail_bound`: `|w| ≤ exp(2|κ|B) exp(-η L)` for `|J| ≤ B`, and
   `|log(1+w)| ≤ (3/2)|w|` when `|w| ≤ 1/2`.

The ODE identification of `m` as a Floquet multiplier (monodromy eigenvalue) is NOT in this
module. Here it enters only as the hypothesis `heig` of item 2.
No sorry, admit, native_decide or custom axioms.
-/

namespace QuantumNLS.RiccatiFloquet

/-- Item 1: the exponential identity behind `s_κ = e^{izL/2}(m + m⁻¹)`. -/
theorem trace_exp_identity (z L κ J : ℂ) :
    Complex.exp (Complex.I * z * L / 2)
        * (Complex.exp (-(Complex.I * z * L / 2) + κ * J)
            + (Complex.exp (-(Complex.I * z * L / 2) + κ * J))⁻¹)
      = Complex.exp (κ * J) * (1 + Complex.exp (Complex.I * z * L - 2 * κ * J)) := by
  have hinv : (Complex.exp (-(Complex.I * z * L / 2) + κ * J))⁻¹
      = Complex.exp (Complex.I * z * L / 2 - κ * J) := by
    rw [← Complex.exp_neg]
    congr 1
    ring
  have e1 : Complex.exp (Complex.I * z * L / 2) * Complex.exp (-(Complex.I * z * L / 2) + κ * J)
      = Complex.exp (κ * J) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have e2 : Complex.exp (Complex.I * z * L / 2) * Complex.exp (Complex.I * z * L / 2 - κ * J)
      = Complex.exp (κ * J) * Complex.exp (Complex.I * z * L - 2 * κ * J) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [hinv, mul_add, e1, e2]
  ring

/-- Item 2: a 2x2 matrix with determinant 1 and eigenvalue `m ≠ 0` has trace `m + m⁻¹`. -/
theorem trace_eq_of_det_one_eigen (M : Matrix (Fin 2) (Fin 2) ℂ) (hdet : M.det = 1) (m : ℂ)
    (hm : m ≠ 0) (heig : (M - m • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0) :
    M.trace = m + m⁻¹ := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.det_fin_two] at heig
  rw [Matrix.trace_fin_two]
  simp at heig
  have key : (M 0 0 + M 1 1) * m = m ^ 2 + 1 := by
    linear_combination hdet - heig
  have hm' : m⁻¹ * m = 1 := inv_mul_cancel₀ hm
  linear_combination m⁻¹ * key - (M 0 0 + M 1 1 - m) * hm'

/-- Item 3a: the modulus of `exp(izL - 2κJ)` with `|J| ≤ B` and real `L, κ`. -/
theorem tail_exp_bound (L κ : ℝ) (z J : ℂ) (B : ℝ) (hJ : ‖J‖ ≤ B) :
    ‖Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)‖
      ≤ Real.exp (2 * |κ| * B) * Real.exp (-(z.im * L)) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hre : (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J).re
      = -(z.im * L) - 2 * κ * J.re := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hJre : |J.re| ≤ B := (Complex.abs_re_le_norm J).trans hJ
  have hκ : κ * J.re ≥ -(|κ| * B) := by
    have h1 : |κ * J.re| ≤ |κ| * B := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hJre (abs_nonneg κ)
    have h2 := neg_abs_le (κ * J.re)
    nlinarith [abs_nonneg (κ * J.re), h1, h2]
  linarith [hκ]

/-- Item 3b: the tail `log(1 + w)` is bounded by `(3/2)|w|` once `|w| ≤ 1/2`. -/
theorem log_tail_bound {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : ‖Complex.log (1 + w)‖ ≤ (3 / 2) * ‖w‖ :=
  Complex.norm_log_one_add_half_le_self hw

/-- Item 3c: combined tail bound `|log(1+w)| ≤ C e^{-η L}` with `C = (3/2) exp(2|κ|B)`,
under the explicit smallness hypothesis `exp(2|κ|B) exp(-ηL) ≤ 1/2`. -/
theorem tail_log_bound (L κ : ℝ) (z J : ℂ) (B : ℝ) (hJ : ‖J‖ ≤ B)
    (hsmall : Real.exp (2 * |κ| * B) * Real.exp (-(z.im * L)) ≤ 1 / 2) :
    ‖Complex.log (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J))‖
      ≤ (3 / 2) * (Real.exp (2 * |κ| * B) * Real.exp (-(z.im * L))) := by
  have hw_le := (tail_exp_bound L κ z J B hJ).trans hsmall
  exact (log_tail_bound hw_le).trans
    (mul_le_mul_of_nonneg_left (tail_exp_bound L κ z J B hJ) (by norm_num))

end QuantumNLS.RiccatiFloquet

#print axioms QuantumNLS.RiccatiFloquet.trace_exp_identity
#print axioms QuantumNLS.RiccatiFloquet.trace_eq_of_det_one_eigen
#print axioms QuantumNLS.RiccatiFloquet.tail_exp_bound
#print axioms QuantumNLS.RiccatiFloquet.tail_log_bound
