import NlsGge.Hierarchy.RiccatiSpatialDerivativeHomogeneousComponentAfterMonomialPrerequisite
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open MvPolynomial

/-- The actual attached Riccati recurrence after projection to ordinary
field degree `d`. The source convolution is kept intact here; the product
projection lemma is a separate step for its degree-index expansion. -/
theorem p_homogeneous_recurrence (k d : ℕ) :
    MvPolynomial.homogeneousComponent d (p (k + 2)) =
      spatialD (MvPolynomial.homogeneousComponent d (p (k + 1))) +
        (Finset.Icc 1 k).attach.sum (fun l =>
          MvPolynomial.homogeneousComponent d
            (MvPolynomial.X (false, 0) *
              (p (k + 1 - l.1) * p l.1))) := by
  rw [p_recurrence k, map_add, spatialD_homogeneousComponent, Finset.mul_sum, map_sum]

end NlsGge.HierarchyRiccati.Core
