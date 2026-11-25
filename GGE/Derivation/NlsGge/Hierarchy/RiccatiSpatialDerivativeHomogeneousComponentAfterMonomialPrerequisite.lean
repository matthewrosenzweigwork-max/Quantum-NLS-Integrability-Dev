import NlsGge.Hierarchy.RiccatiSpatialDerivativeOrdinaryDegreeMonomialPrerequisiteSecond
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open MvPolynomial

noncomputable section

/-- The actual spatial derivative of a source monomial is homogeneous in the
same ordinary field degree. This is proved from the pinned derivation sum. -/
theorem spatialD_monomial_isHomogeneous (m : Jet →₀ ℕ) (r : ℤ) :
    (spatialD (MvPolynomial.monomial m r)).IsHomogeneous m.degree := by
  change MvPolynomial.mkDerivation ℤ
    (fun v : Jet => MvPolynomial.X (v.1, v.2 + 1)) (MvPolynomial.monomial m r) |>.IsHomogeneous m.degree
  rw [MvPolynomial.mkDerivation_monomial]
  change r • (m.sum fun v k =>
    MvPolynomial.monomial (m - Finsupp.single v 1) (k : ℤ) *
      MvPolynomial.X (v.1, v.2 + 1)) ∈ MvPolynomial.homogeneousSubmodule Jet ℤ m.degree
  apply (MvPolynomial.homogeneousSubmodule Jet ℤ m.degree).smul_mem
  apply MvPolynomial.IsHomogeneous.sum
  intro v hv
  exact spatialDerivativeMonomialTerm_isHomogeneous m v (m v) hv

/-- The homogeneous projection commutes with `spatialD` on a monomial. -/
theorem spatialD_homogeneousComponent_monomial
    (d : ℕ) (m : Jet →₀ ℕ) (r : ℤ) :
    MvPolynomial.homogeneousComponent d (spatialD (MvPolynomial.monomial m r)) =
      spatialD (MvPolynomial.homogeneousComponent d (MvPolynomial.monomial m r)) := by
  rw [MvPolynomial.homogeneousComponent_of_mem (spatialD_monomial_isHomogeneous m r),
    MvPolynomial.homogeneousComponent_of_mem
      (MvPolynomial.isHomogeneous_monomial r rfl)]
  by_cases h : d = m.degree <;> simp [h]

/-- Ordinary homogeneous projection commutes with the actual source spatial
jet derivative on every polynomial. -/
theorem spatialD_homogeneousComponent (d : ℕ) (P : Poly) :
    MvPolynomial.homogeneousComponent d (spatialD P) =
      spatialD (MvPolynomial.homogeneousComponent d P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial m r => exact spatialD_homogeneousComponent_monomial d m r
  | add P Q hP hQ => simp [hP, hQ, map_add]

end

end NlsGge.HierarchyRiccati.Core
