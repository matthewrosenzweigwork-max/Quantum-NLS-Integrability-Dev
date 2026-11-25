import NlsGge.Hierarchy.RiccatiLeadingComponentsAfterHomogeneousRecurrenceAfterDirectLowDegreeProof
import NlsGge.Hierarchy.RiccatiHomogeneousComponentSuccessorMulGeneratorThird
import NlsGge.Hierarchy.RiccatiLowOrderAlgebraAfterCore
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open MvPolynomial

/-- The actual formal charge density has the expected degree-two source term.
This is an ordinary homogeneous-component identity, not an integral or
spectral-charge statement. -/
theorem formalChargeIntegrand_degreeTwoComponent (j : ℕ) :
    MvPolynomial.homogeneousComponent 2 (formalChargeIntegrand j) =
      MvPolynomial.C ((-1 : ℤ) ^ j) * MvPolynomial.X (false, 0) *
        MvPolynomial.X (true, 2 * j) := by
  unfold formalChargeIntegrand
  rw [mul_assoc, MvPolynomial.homogeneousComponent_C_mul,
    homogeneousComponent_succ_mul_X,
    p_linear_homogeneous_component (2 * j + 1) (by omega)]
  have hindex : 2 * j + 1 - 1 = 2 * j := by omega
  rw [hindex]
  have hsign : (-1 : ℤ) ^ (j + 1) = -((-1 : ℤ) ^ j) := by
    rw [pow_succ]
    ring
  rw [hsign]
  simp [mul_assoc]

end NlsGge.HierarchyRiccati.Core
