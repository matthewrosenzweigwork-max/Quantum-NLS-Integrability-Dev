import NlsGge.Hierarchy.RiccatiFormalChargeDegreeTwoComponentAfterDirectLeadingProofThirdNormalized
import NlsGge.Hierarchy.RiccatiLowOrderAlgebraAfterCore
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open MvPolynomial

noncomputable section

/-- The actual all-order quadratic polynomial identified by the checked
degree-two component theorem. -/
def formalChargeQuadraticMainTerm (j : ℕ) : Poly :=
  MvPolynomial.C ((-1 : ℤ) ^ j) * MvPolynomial.X (false, 0) *
    MvPolynomial.X (true, 2 * j)

/-- The remainder after subtracting the actual quadratic component. -/
def formalChargeNonlinearRemainder (j : ℕ) : Poly :=
  formalChargeIntegrand j - formalChargeQuadraticMainTerm j

/-- At every exponent of ordinary degree two, the coefficient in the actual
charge equals the coefficient in its checked quadratic component. -/
theorem formalCharge_coefficient_degreeTwo (j : ℕ) (m : Jet →₀ ℕ)
    (hm : m.degree = 2) :
    (formalChargeIntegrand j).coeff m = (formalChargeQuadraticMainTerm j).coeff m := by
  have h := congrArg (fun P : Poly => P.coeff m)
    (formalChargeIntegrand_degreeTwoComponent j)
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos hm] at h
  simpa [formalChargeQuadraticMainTerm] using h

/-- The checked quadratic subtraction removes every coefficient of exponent
degree two, rather than merely identifying one candidate monomial. -/
theorem formalChargeNonlinearRemainder_coeff_degreeTwo_eq_zero
    (j : ℕ) (m : Jet →₀ ℕ) (hm : m.degree = 2) :
    (formalChargeNonlinearRemainder j).coeff m = 0 := by
  rw [formalChargeNonlinearRemainder, MvPolynomial.coeff_sub,
    formalCharge_coefficient_degreeTwo j m hm, sub_self]

/-- No exponent of ordinary degree two survives in the actual nonlinear
remainder. -/
theorem formalChargeNonlinearRemainder_support_degree_ne_two
    (j : ℕ) (m : Jet →₀ ℕ)
    (hm : m ∈ (formalChargeNonlinearRemainder j).support) : m.degree ≠ 2 := by
  intro hdegree
  have hnonzero : (formalChargeNonlinearRemainder j).coeff m ≠ 0 :=
    Finsupp.mem_support_iff.mp hm
  have hzero := formalChargeNonlinearRemainder_coeff_degreeTwo_eq_zero j m hdegree
  exact hnonzero hzero

end

end NlsGge.HierarchyRiccati.Core
