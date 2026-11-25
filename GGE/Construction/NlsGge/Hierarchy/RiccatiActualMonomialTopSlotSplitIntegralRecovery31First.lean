import NlsGge.Hierarchy.RiccatiTopJetSlotMultiplicityAtMostTwoMinimumRecovery30Third
import NlsGge.Hierarchy.RiccatiSmoothJetDerivativeAfterProductPrerequisite
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory

/-- For the actual Riccati jet evaluator, the source monomial factors as the
product over the top-order slots and the product over all remaining slots.
The Finsupp filters retain repeated factors with their full multiplicity. -/
theorem riccatiActualMonomial_topSlotSplitPointwiseRecovery31First
    (m : ℕ) (u : ℝ → ℂ) (x : ℝ) (c : ℤ) (q : Jet →₀ ℕ) :
    riccatiJetEvaluation u x (MvPolynomial.monomial q c) =
      (c : ℂ) *
        ((q.filter (fun v : Jet => v.2 + 1 = m)).prod
          (fun v n => riccatiJetFunction u v x ^ n)) *
        ((q.filter (fun v : Jet => ¬ v.2 + 1 = m)).prod
          (fun v n => riccatiJetFunction u v x ^ n)) := by
  classical
  let top : Jet → Prop := fun v => v.2 + 1 = m
  let factor : Jet → ℕ → ℂ := fun v n => riccatiJetFunction u v x ^ n
  have hsplit :
      (q.filter top).prod factor * (q.filter (fun v => ¬ top v)).prod factor =
        q.prod factor := by
    exact Finsupp.prod_filter_mul_prod_filter_not top q factor
  calc
    riccatiJetEvaluation u x (MvPolynomial.monomial q c) =
        (c : ℂ) * q.prod factor := by
          simp [riccatiJetEvaluation, polynomialEvaluation, factor]
    _ = (c : ℂ) * ((q.filter top).prod factor *
          (q.filter (fun v => ¬ top v)).prod factor) := by rw [← hsplit]
    _ = _ := by simp [top, factor, mul_assoc]

/-- The exact period-one interval integral of the actual source monomial is
the integral of its top-slot/lower-slot factorization. This is a literal
integrand identity; it does not assume integrability, periodicity, or a
Sobolev extension. -/
theorem riccatiActualMonomial_topSlotSplitIntegralRecovery31First
    (m : ℕ) (u : ℝ → ℂ) (c : ℤ) (q : Jet →₀ ℕ) :
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (MvPolynomial.monomial q c)) =
      ∫ x in (0 : ℝ)..1,
        (c : ℂ) *
          ((q.filter (fun v : Jet => v.2 + 1 = m)).prod
            (fun v n => riccatiJetFunction u v x ^ n)) *
          ((q.filter (fun v : Jet => ¬ v.2 + 1 = m)).prod
            (fun v n => riccatiJetFunction u v x ^ n)) := by
  apply intervalIntegral.integral_congr
  intro x hx
  exact riccatiActualMonomial_topSlotSplitPointwiseRecovery31First m u x c q

/-- Under the actual derivative-count hypothesis, the first filtered product
contains at most two top-order slots, counted with multiplicity. -/
theorem riccatiActualMonomial_topSlotSplit_count_le_twoRecovery31First
    (m : ℕ) (hm : 2 ≤ m) (q : Jet →₀ ℕ)
    (hD : riccatiJetDerivativeOrderSumNativeRecovery q ≤ 2 * m - 2) :
    riccatiTopJetSlotMultiplicityMinimumRecovery30Third m q ≤ 2 := by
  exact riccatiTopJetSlotMultiplicity_le_twoMinimumRecovery30Third m hm q hD

end NlsGge.HierarchyRiccati.Core

end
