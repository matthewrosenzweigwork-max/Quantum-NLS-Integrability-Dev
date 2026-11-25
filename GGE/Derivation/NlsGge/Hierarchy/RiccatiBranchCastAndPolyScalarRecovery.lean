import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

/-- The integer cast into the actual jet-polynomial ring is its `C` map.
Both the applied Int cast and the concrete MvPolynomial coefficient ring are
exposed explicitly, avoiding a rewrite through the `Poly` abbreviation. -/
theorem riccatiPoly_intCast_eq_CNativeRecovery28 (c : ℤ) :
    (c : Poly) = MvPolynomial.C c := by
  change (Int.castRingHom (MvPolynomial Jet ℤ)) c = MvPolynomial.C c
  rw [← algebraMap_int_eq]
  change (algebraMap ℤ (MvPolynomial Jet ℤ)) c = MvPolynomial.C c
  rw [MvPolynomial.algebraMap_eq]

/-- The actual polynomial self-scalar action in the pinned MvPolynomial ring
is multiplication, and multiplying by a jet variable increments its exponent
by the corresponding single Finsupp. -/
theorem riccatiPoly_monomial_smul_X_eqNativeRecovery28
    (s : Jet →₀ ℕ) (a : ℤ) (v : Jet) :
    MvPolynomial.monomial s a • MvPolynomial.X v =
      MvPolynomial.monomial (s + Finsupp.single v 1) a := by
  rw [smul_eq_mul, MvPolynomial.X, MvPolynomial.monomial_mul_monomial]
  simp

/-- Exact one-branch product after exposing the cast and polynomial
self-scalar action; this is the algebraic kernel used to rebuild finite IBP
branch expansion. -/
theorem riccatiPoly_IBP_branch_productNativeRecovery28
    (r : Jet →₀ ℕ) (c : ℤ) (v w : Jet) :
    MvPolynomial.X v * (c : Poly) *
        (MvPolynomial.monomial (r - Finsupp.single w 1) (r w : ℤ) •
          MvPolynomial.X w) =
      MvPolynomial.monomial
        ((r - Finsupp.single w 1) + Finsupp.single w 1 + Finsupp.single v 1)
        (c * (r w : ℤ)) := by
  rw [riccatiPoly_intCast_eq_CNativeRecovery28,
    riccatiPoly_monomial_smul_X_eqNativeRecovery28]
  rw [MvPolynomial.X]
  calc
    MvPolynomial.monomial (Finsupp.single v 1) 1 * MvPolynomial.C c *
        MvPolynomial.monomial
          ((r - Finsupp.single w 1) + Finsupp.single w 1) (r w : ℤ) =
      MvPolynomial.C c *
        MvPolynomial.monomial
          ((r - Finsupp.single w 1) + Finsupp.single w 1) (r w : ℤ) *
        MvPolynomial.monomial (Finsupp.single v 1) 1 := by
          ac_rfl
    _ = MvPolynomial.monomial
          ((r - Finsupp.single w 1) + Finsupp.single w 1)
          (c * (r w : ℤ)) *
        MvPolynomial.monomial (Finsupp.single v 1) 1 := by
          rw [MvPolynomial.C_mul_monomial]
    _ = MvPolynomial.monomial
          (((r - Finsupp.single w 1) + Finsupp.single w 1) +
            Finsupp.single v 1)
          (c * (r w : ℤ) * 1) := by
          rw [MvPolynomial.monomial_mul_monomial]
    _ = _ := by simp

end NlsGge.HierarchyRiccati.Core
