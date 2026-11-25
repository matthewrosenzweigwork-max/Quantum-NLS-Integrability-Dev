import NlsGge.Hierarchy.RiccatiBranchCastAndPolyScalarRecovery
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

/-- The branch polynomial arising from differentiating a residual jet `w`
contains the shifted jet `w+1`, while the derivative multiplicity removes one
copy of the unshifted `w`. This is the exact product shape in the actual
finite-support derivation expansion. -/
theorem riccatiPoly_shifted_IBP_branch_productNativeRecovery28Second
    (r : Jet →₀ ℕ) (c : ℤ) (v w : Jet) :
    MvPolynomial.X (v.1, v.2 - 1) * (c : Poly) *
        (MvPolynomial.monomial (r - Finsupp.single w 1) (r w : ℤ) •
          MvPolynomial.X (w.1, w.2 + 1)) =
      MvPolynomial.monomial
        ((r - Finsupp.single w 1) +
          Finsupp.single (w.1, w.2 + 1) 1 +
          Finsupp.single (v.1, v.2 - 1) 1)
        (c * (r w : ℤ)) := by
  rw [riccatiPoly_intCast_eq_CNativeRecovery28,
    riccatiPoly_monomial_smul_X_eqNativeRecovery28]
  rw [MvPolynomial.X]
  calc
    MvPolynomial.monomial (Finsupp.single (v.1, v.2 - 1) 1) 1 *
        MvPolynomial.C c *
          MvPolynomial.monomial
            ((r - Finsupp.single w 1) + Finsupp.single (w.1, w.2 + 1) 1)
            (r w : ℤ) =
      MvPolynomial.C c *
          MvPolynomial.monomial
            ((r - Finsupp.single w 1) + Finsupp.single (w.1, w.2 + 1) 1)
            (r w : ℤ) *
        MvPolynomial.monomial (Finsupp.single (v.1, v.2 - 1) 1) 1 := by
          ac_rfl
    _ = MvPolynomial.monomial
          ((r - Finsupp.single w 1) + Finsupp.single (w.1, w.2 + 1) 1)
          (c * (r w : ℤ)) *
        MvPolynomial.monomial (Finsupp.single (v.1, v.2 - 1) 1) 1 := by
          rw [MvPolynomial.C_mul_monomial]
    _ = MvPolynomial.monomial
          (((r - Finsupp.single w 1) + Finsupp.single (w.1, w.2 + 1) 1) +
            Finsupp.single (v.1, v.2 - 1) 1)
          (c * (r w : ℤ) * 1) := by
          rw [MvPolynomial.monomial_mul_monomial]
    _ = _ := by
          simpa only [mul_one]

end NlsGge.HierarchyRiccati.Core
