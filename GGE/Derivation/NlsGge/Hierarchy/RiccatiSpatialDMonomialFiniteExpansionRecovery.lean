import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import Mathlib.Algebra.MvPolynomial.Derivation

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open MvPolynomial

/-- Exact finite-support expansion of the actual spatial derivation on a
monomial. The coefficient `k` is the multiplicity of the differentiated
residual jet. -/
theorem spatialD_monomial_actual_factor_expansionNativeRecovery
    (m : Jet →₀ ℕ) (c : ℤ) :
    spatialD (MvPolynomial.monomial m c) =
      c • m.sum (fun w k =>
        MvPolynomial.monomial (m - Finsupp.single w 1) (k : ℤ) •
          MvPolynomial.X (w.1, w.2 + 1)) := by
  simpa [spatialD] using
    (MvPolynomial.mkDerivation_monomial (R := ℤ) (σ := Jet) (A := Poly)
      (fun w : Jet => MvPolynomial.X (w.1, w.2 + 1)) m c)

end NlsGge.HierarchyRiccati.Core
