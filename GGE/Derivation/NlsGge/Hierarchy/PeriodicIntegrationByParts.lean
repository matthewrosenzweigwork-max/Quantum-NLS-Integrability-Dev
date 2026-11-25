import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
E06.04 periodic integration by parts on the paper's unit-period circle.
This is a concrete scalar lemma on smooth periodic complex-valued functions;
it does not assume an identity modulo total derivatives.
-/

namespace NlsGge.HierarchyRiccati

/-- Unit-period integration by parts with explicit derivative integrability.
The periodicity hypotheses are used to cancel the boundary trace at 0 and 1. -/
theorem unitPeriod_integral_mul_deriv_eq_neg_deriv_mul
    {f g f' g' : ℝ → ℂ}
    (hfper : Function.Periodic f 1) (hgper : Function.Periodic g 1)
    (hf : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' x) x)
    (hf' : IntervalIntegrable f' MeasureTheory.volume 0 1)
    (hg' : IntervalIntegrable g' MeasureTheory.volume 0 1) :
    (∫ x in (0 : ℝ)..1, f x * g' x) =
      -(∫ x in (0 : ℝ)..1, f' x * g x) := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => hf x (by simpa using hx))
    (fun x hx => hg x (by simpa using hx)) hf' hg']
  have hF : f 1 = f 0 := by simpa using hfper 0
  have hG : g 1 = g 0 := by simpa using hgper 0
  rw [hF, hG, sub_self, zero_sub]

end NlsGge.HierarchyRiccati
