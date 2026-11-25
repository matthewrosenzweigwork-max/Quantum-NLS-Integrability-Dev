import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open MvPolynomial

noncomputable section

/-- A summand in the pinned `mkDerivation_monomial` formula for `spatialD`:
one jet factor is removed and a first-order shifted jet is inserted. -/
def spatialDerivativeMonomialTerm (m : Jet →₀ ℕ) (v : Jet) (k : ℕ) : Poly :=
  MvPolynomial.monomial (m - Finsupp.single v 1) (k : ℤ) *
    MvPolynomial.X (v.1, v.2 + 1)

/-- The exponent change in one source spatial-derivative summand preserves
ordinary total field degree. -/
theorem spatialDerivativeMonomialExponent_degree
    (m : Jet →₀ ℕ) (v : Jet) (hv : v ∈ m.support) :
    (m - Finsupp.single v 1 + Finsupp.single (v.1, v.2 + 1) 1).degree =
      m.degree := by
  have hne : m v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hcancel : m - Finsupp.single v 1 + Finsupp.single v 1 = m :=
    Finsupp.sub_add_single_one_cancel hne
  have hdegree : (m - Finsupp.single v 1).degree + 1 = m.degree := by
    calc
      (m - Finsupp.single v 1).degree + 1 =
          (m - Finsupp.single v 1).degree + (Finsupp.single v 1).degree := by
            simp
      _ = (m - Finsupp.single v 1 + Finsupp.single v 1).degree :=
        (Finsupp.degree.map_add _ _).symm
      _ = m.degree := congrArg Finsupp.degree hcancel
  calc
    _ = (m - Finsupp.single v 1).degree +
        (Finsupp.single (v.1, v.2 + 1) 1).degree :=
          Finsupp.degree.map_add _ _
    _ = (m - Finsupp.single v 1).degree + 1 := by simp
    _ = m.degree := hdegree

/-- Every individual monomial summand in the spatial derivative has the
same homogeneous degree as its source monomial. -/
theorem spatialDerivativeMonomialTerm_isHomogeneous
    (m : Jet →₀ ℕ) (v : Jet) (k : ℕ) (hv : v ∈ m.support) :
    (spatialDerivativeMonomialTerm m v k).IsHomogeneous m.degree := by
  have hmonomial :
      (MvPolynomial.monomial (m - Finsupp.single v 1) (k : ℤ) : Poly).IsHomogeneous
        (m - Finsupp.single v 1).degree :=
    MvPolynomial.isHomogeneous_monomial _ rfl
  have hgenerator :
      (MvPolynomial.X (v.1, v.2 + 1) : Poly).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X _ _
  have hproduct := hmonomial.mul hgenerator
  have hdegree : (m - Finsupp.single v 1).degree + 1 = m.degree := by
    calc
      (m - Finsupp.single v 1).degree + 1 =
          (m - Finsupp.single v 1 + Finsupp.single (v.1, v.2 + 1) 1).degree := by
            rw [Finsupp.degree.map_add]
            simp
      _ = m.degree := spatialDerivativeMonomialExponent_degree m v hv
  simpa [spatialDerivativeMonomialTerm, hdegree] using hproduct

end

end NlsGge.HierarchyRiccati.Core
