import QuantumNLS.TerraMultiRound65FifthRecursion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! A periodic integration-by-parts identity used in the printed proof. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace QuantumNLS.TerraMultiRound65PeriodicIBP

theorem periodic_integration_by_parts (L : ℝ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (pf : Function.Periodic f L) (pg : Function.Periodic g L) :
    (∫ x in (0 : ℝ)..L, f x * deriv g x) =
      -∫ x in (0 : ℝ)..L, deriv f x * g x := by
  have df := (contDiff_infty_iff_deriv.mp hf).1
  have dg := (contDiff_infty_iff_deriv.mp hg).1
  have cf := (contDiff_infty_iff_deriv.mp hf).2.continuous
  have cg := (contDiff_infty_iff_deriv.mp hg).2.continuous
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => (df x).hasDerivAt) (fun x _ => (dg x).hasDerivAt)
    (cf.intervalIntegrable 0 L) (cg.intervalIntegrable 0 L)
  have hf0 : f L = f 0 := by simpa using pf 0
  have hg0 : g L = g 0 := by simpa using pg 0
  rw [hf0, hg0, sub_self, zero_sub] at h
  exact h

#print axioms periodic_integration_by_parts
end QuantumNLS.TerraMultiRound65PeriodicIBP
