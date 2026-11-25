import Mathlib

/-!
# R-3FEAD88B blocker 2, stage E1: periodic H^a weights and the resolvent bound

Source convention (DEF-002, `source/chapters/definitions.tex:15`): for `s ≥ 0`, `H^s(T_L)` consists of fields `u` with
`∑_n (1 + |2π n / L|)^(2s) |û(n)|² < ∞`. Here a field is identified with its Fourier coefficient sequence
`c : ℤ → ℂ`, and the squared norm is valued in `ENNReal` (so no summability side conditions arise).

The Fourier multiplier of `∂x` on mode `k` is `i · 2πk/L`, so `R_z = (∂x − i z)⁻¹` acts on mode `k` by
`c k / (i (2πk/L − z))`. Since `|2πk/L − z| ≥ |Im z| = η`, the multiplier has modulus at most `1/η`.

Proved here: `hsq_resolvent_le`, the squared operator bound `‖R_z c‖²_{H^a} ≤ η⁻² ‖c‖²_{H^a}` for `η = Im z > 0`
(all `a`, all `L`), i.e. `‖R_z‖_{H^a → H^a} ≤ η⁻¹`. Standard axioms only.
-/

set_option autoImplicit false
noncomputable section
open Complex

namespace QuantumNLS.RiccatiSobolevE1

/-- Frequency `2π k / L` of mode `k` on the circle of length `L`. -/
def freq (L : ℝ) (k : ℤ) : ℝ := 2 * Real.pi * (k : ℝ) / L

/-- Sobolev weight `(1 + |2π k / L|)^(2a)` (DEF-002). -/
def wt (L a : ℝ) (k : ℤ) : ℝ := (1 + |freq L k|) ^ (2 * a)

/-- Squared periodic H^a norm of a Fourier coefficient sequence, valued in `[0, ∞]`. -/
def hsq (L a : ℝ) (c : ℤ → ℂ) : ENNReal :=
  ∑' k : ℤ, ENNReal.ofReal (wt L a k * ‖c k‖ ^ 2)

/-- The resolvent `(∂x − i z)⁻¹` on Fourier coefficients: mode `k` is multiplied by `1 / (i (2πk/L − z))`. -/
def resolvent (L : ℝ) (z : ℂ) (c : ℤ → ℂ) : ℤ → ℂ :=
  fun k => c k / (Complex.I * (((freq L k : ℝ) : ℂ) - z))

theorem wt_nonneg (L a : ℝ) (k : ℤ) : 0 ≤ wt L a k :=
  Real.rpow_nonneg (by positivity) _

/-- Pointwise multiplier bound: `|c / (i (f − z))| ≤ (Im z)⁻¹ |c|` for real `f` and `Im z > 0`. -/
theorem norm_div_I_mul_le (c : ℂ) (f : ℝ) (z : ℂ) (hz : 0 < z.im) :
    ‖c / (Complex.I * ((f : ℂ) - z))‖ ≤ z.im⁻¹ * ‖c‖ := by
  have hw : z.im ≤ ‖((f : ℂ) - z)‖ := by
    have h := Complex.abs_im_le_norm ((f : ℂ) - z)
    have him : ((f : ℂ) - z).im = -z.im := by simp
    rw [him, abs_neg, abs_of_pos hz] at h
    exact h
  have hpos : 0 < ‖((f : ℂ) - z)‖ := lt_of_lt_of_le hz hw
  rw [norm_div, norm_mul, Complex.norm_I, one_mul]
  calc ‖c‖ / ‖((f : ℂ) - z)‖ ≤ ‖c‖ / z.im :=
        div_le_div_of_nonneg_left (norm_nonneg c) hz hw
    _ = z.im⁻¹ * ‖c‖ := by rw [div_eq_inv_mul]

/-- Squared operator bound for the resolvent in the periodic H^a norm: `‖R_z c‖² ≤ (Im z)⁻² ‖c‖²`. -/
theorem hsq_resolvent_le {L : ℝ} (a : ℝ) (z : ℂ) (hz : 0 < z.im) (c : ℤ → ℂ) :
    hsq L a (resolvent L z c) ≤ ENNReal.ofReal ((z.im⁻¹) ^ 2) * hsq L a c := by
  unfold hsq
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hn := norm_div_I_mul_le (c k) (freq L k) z hz
  have hn2 : ‖c k / (Complex.I * (((freq L k : ℝ) : ℂ) - z))‖ ^ 2 ≤ (z.im⁻¹) ^ 2 * ‖c k‖ ^ 2 := by
    have h0 : 0 ≤ ‖c k / (Complex.I * (((freq L k : ℝ) : ℂ) - z))‖ := norm_nonneg _
    have := pow_le_pow_left₀ h0 hn 2
    rw [mul_pow] at this
    exact this
  have hw := wt_nonneg L a k
  calc wt L a k * ‖resolvent L z c k‖ ^ 2
      = wt L a k * ‖c k / (Complex.I * (((freq L k : ℝ) : ℂ) - z))‖ ^ 2 := rfl
    _ ≤ wt L a k * ((z.im⁻¹) ^ 2 * ‖c k‖ ^ 2) := mul_le_mul_of_nonneg_left hn2 hw
    _ = (z.im⁻¹) ^ 2 * (wt L a k * ‖c k‖ ^ 2) := by ring

end QuantumNLS.RiccatiSobolevE1

#print axioms QuantumNLS.RiccatiSobolevE1.hsq_resolvent_le
