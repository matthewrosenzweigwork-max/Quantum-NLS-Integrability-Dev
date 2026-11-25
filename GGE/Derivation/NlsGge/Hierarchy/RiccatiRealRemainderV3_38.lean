import NlsGge.Hierarchy.RiccatiRemainderIntegralForm38
import NlsGge.Hierarchy.RiccatiRealQ2Q4Formula38
import NlsGge.Hierarchy.RiccatiQ6QuarticContinuity38
import Mathlib.Tactic

/-! Batch 38, A01: explicit real form of the finite-order remainder `V_3`
(`C:prop:negative`, paper/v2.tex lines 2427-2433), with the local
(recursion-defined) charges `Q_{2j} = ∫₀¹ (-1)^{j+1} u p_{2j+1}`:
for a real smooth period-one field
`V_3(u) = β₁∫u⁴ + β₂∫(10u²u'² + 2u⁶) + β₃(F(u) + ∫(70u⁴u'² + 5u⁸))`
with `F(u) = ∫(14u²u''² - 7u'⁴)` (`C:eq:Q6real`). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot
open MeasureTheory
open scoped ContDiff

private theorem iterDeriv_cont38 (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (k : ℕ) :
    Continuous (iteratedDeriv k u) :=
  hu.continuous_iteratedDeriv k (by exact_mod_cast le_top)

private theorem norm_iteratedDeriv_ofReal_sq38 (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
    (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (fun y => (u y : ℂ)) x‖ ^ 2 = (iteratedDeriv k u x) ^ 2 := by
  rw [iteratedDeriv_ofReal38 u hu k, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Explicit real form of `V_3` with the local charges. -/
theorem remainderV3_real38 (β : ℕ → ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (hU : ContDiff ℝ ∞ (fun y => (u y : ℂ)))
    (hUper : Function.Periodic (fun y => (u y : ℂ)) 1) :
    remainderV38 3 β (fun y => (u y : ℂ)) hU hUper =
      β 1 * (∫ x in (0:ℝ)..1, (u x) ^ 4) +
      β 2 * (∫ x in (0:ℝ)..1, (10 * (u x) ^ 2 * (deriv u x) ^ 2 + 2 * (u x) ^ 6)) +
      β 3 * ((∫ x in (0:ℝ)..1,
          quarticDensity38 (u x) (deriv u x) (iteratedDeriv 2 u x)) +
        ∫ x in (0:ℝ)..1, (70 * (u x) ^ 4 * (deriv u x) ^ 2 + 5 * (u x) ^ 8)) := by
  have c0 : Continuous u := hu.continuous
  have c1 : Continuous (deriv u) := hu.continuous_deriv (by exact_mod_cast le_top)
  have c2 := iterDeriv_cont38 u hu 2
  have c3 := iterDeriv_cont38 u hu 3
  have hd1 : iteratedDeriv 1 u = deriv u := iteratedDeriv_one
  rw [(remainderV38_integral_form 3 β _ hU hUper).2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    norm_iteratedDeriv_ofReal_sq38 u hu]
  rw [realQ0_local_formula38 u hu hper, realQ2_local_formula38 u hu hper,
    realQ4_local_formula38 u hu hper, realQ6_local_formula38 u hu hper]
  simp only [Complex.ofReal_re, iteratedDeriv_zero, hd1]
  have e1 : (∫ x in (0:ℝ)..1, ((deriv u x) ^ 2 + (u x) ^ 4)) -
      ∫ x in (0:ℝ)..1, (deriv u x) ^ 2 = ∫ x in (0:ℝ)..1, (u x) ^ 4 := by
    rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    congr 1; funext x; ring
  have e2 : (∫ x in (0:ℝ)..1, ((iteratedDeriv 2 u x) ^ 2 + 10 * (u x) ^ 2 * (deriv u x) ^ 2 +
      2 * (u x) ^ 6)) - ∫ x in (0:ℝ)..1, (iteratedDeriv 2 u x) ^ 2 =
      ∫ x in (0:ℝ)..1, (10 * (u x) ^ 2 * (deriv u x) ^ 2 + 2 * (u x) ^ 6) := by
    rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    congr 1; funext x; ring
  have e3 : (∫ x in (0:ℝ)..1, ((iteratedDeriv 3 u x) ^ 2 +
      14 * (u x) ^ 2 * (iteratedDeriv 2 u x) ^ 2 - 7 * (deriv u x) ^ 4 +
      70 * (u x) ^ 4 * (deriv u x) ^ 2 + 5 * (u x) ^ 8)) -
      ∫ x in (0:ℝ)..1, (iteratedDeriv 3 u x) ^ 2 =
      (∫ x in (0:ℝ)..1, quarticDensity38 (u x) (deriv u x) (iteratedDeriv 2 u x)) +
        ∫ x in (0:ℝ)..1, (70 * (u x) ^ 4 * (deriv u x) ^ 2 + 5 * (u x) ^ 8) := by
    rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
      ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; unfold quarticDensity38; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    congr 1; funext x; unfold quarticDensity38; ring
  rw [e1, e2, e3, sub_self, mul_zero, zero_add]

end NlsGge.HierarchyRiccati.Core

end
