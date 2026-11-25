import NlsGge.Hierarchy.RiccatiAttachedRecursionCore

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

theorem spatialD_natCast_eq_zero (n : ℕ) :
    spatialD (n : Poly) = 0 := by
  exact spatialD.map_natCast n

theorem spatialD_four_eq_zero : spatialD (4 : Poly) = 0 := by
  change spatialD (4 : ℕ) = 0
  exact spatialD_natCast_eq_zero 4

end NlsGge.HierarchyRiccati.Core
