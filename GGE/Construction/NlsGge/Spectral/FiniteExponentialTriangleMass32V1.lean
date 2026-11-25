import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations

/-- Exact finite affine exponential integral. Both signs of the coefficient
are allowed, and division is justified by the explicit nonzero premise. -/
theorem finiteAffineExponentialIntegral32 (a b c d : ℝ) (hc : c ≠ 0) :
    (∫ x in a..b, Real.exp (c * (x - d))) =
      (Real.exp (c * (b - d)) - Real.exp (c * (a - d))) / c := by
  have hd (x : ℝ) : HasDerivAt
      (fun x : ℝ => Real.exp (c * (x - d)) / c)
      (Real.exp (c * (x - d))) x := by
    have h := (((hasDerivAt_id x).sub_const d).const_mul c).exp.div_const c
    convert h using 1 <;> simp [hc]
  have hi : IntervalIntegrable (fun x : ℝ => Real.exp (c * (x - d))) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
  ring

/-- The past-pointing triangle kernel has finite mass at most 1/c for c>0.
This is a scalar ingredient; the actual potential-product Fubini and L²
bounds must still be supplied before claiming the trace estimate. -/
theorem finitePastExponentialMass_le32 (a b c : ℝ) (hc : 0 < c) :
    (∫ x in a..b, Real.exp (-c * (b - x))) ≤ 1 / c := by
  have heq : (fun x : ℝ => Real.exp (-c * (b - x))) =
      (fun x => Real.exp (c * (x - b))) := by
    funext x
    congr 1
    ring
  rw [heq, finiteAffineExponentialIntegral32 a b c b hc.ne']
  simp only [sub_self, mul_zero, Real.exp_zero]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_nonneg (c * (a-b))]) hc.le

/-- The future-pointing kernel has the same finite mass bound. No extension
to a half-line or integrability assumption at infinity is used. -/
theorem finiteFutureExponentialMass_le32 (a b c : ℝ) (hc : 0 < c) :
    (∫ x in a..b, Real.exp (-c * (x - a))) ≤ 1 / c := by
  rw [finiteAffineExponentialIntegral32 a b (-c) a (neg_ne_zero.mpr hc.ne')]
  simp only [sub_self, mul_zero, Real.exp_zero]
  have heq : (Real.exp (-c * (b-a)) - 1) / -c =
      (1 - Real.exp (-c * (b-a))) / c := by ring
  rw [heq]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_nonneg (-c * (b-a))]) hc.le

end NlsGge.SpectralFoundations
end
