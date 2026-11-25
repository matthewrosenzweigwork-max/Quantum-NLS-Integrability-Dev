import NlsGge.Hierarchy.RiccatiQ4SmoothPeriodicIdentityAfterEvaluationPrerequisitesSecond
import NlsGge.Hierarchy.RiccatiQ4ComplexDensityAlgebraAfterConjugateRealPartPrerequisite
import NlsGge.Hierarchy.RiccatiQ4IteratedDerivStarPrerequisiteThird
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati

open scoped ComplexConjugate

def q4SmoothLowerOrderRealDensityAfterCheckedPrerequisites (u : ℝ → ℂ) (x : ℝ) : ℝ :=
  2 * Complex.re ((star (u x) * iteratedDeriv 1 u x) ^ 2) +
    8 * ‖u x‖ ^ 2 * ‖iteratedDeriv 1 u x‖ ^ 2 +
    2 * ‖u x‖ ^ 6

theorem q4EnergyDensity_eq_h2_leading_add_lower_order_after_checked_prerequisites
    (u : ℝ → ℂ) (x : ℝ) :
    Complex.re (q4EnergyDensityAfterEvaluationPrerequisites u x) =
      ‖iteratedDeriv 2 u x‖ ^ 2 +
        q4SmoothLowerOrderRealDensityAfterCheckedPrerequisites u x := by
  let c : ℂ := u x
  let d : ℂ := iteratedDeriv 1 u x
  let e : ℂ := iteratedDeriv 2 u x
  have hstar1 : iteratedDeriv 1 (fun y => star (u y)) x = star d := by
    exact congrFun (iteratedDeriv_star_prerequisite u 1) x
  have hstar2 : iteratedDeriv 2 (fun y => star (u y)) x = star e := by
    exact congrFun (iteratedDeriv_star_prerequisite u 2) x
  unfold q4EnergyDensityAfterEvaluationPrerequisites
  rw [hstar1, hstar2]
  simpa [c, d, e, q4SmoothLowerOrderRealDensityAfterCheckedPrerequisites] using
    q4ComplexDensityAlgebraAfterConjugateRealPartPrerequisite c d e

end NlsGge.HierarchyRiccati

end
