import NlsGge.Weights.SpatialJensen
import NlsGge.Hierarchy.RiccatiFiniteFourierPlaneQ2Identity

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati

open NlsGge.Pilot
open NlsGge.Weights
open MeasureTheory

/-- The L² norm of the actual finite-plane derivative is its physical
probability-Haar square integral. The equality uses the already proved
finite-plane Parseval identities on both sides. -/
theorem finitePlane_derivative_norm_sq_eq_spatial_integral
    (N : ℕ) (z : FourierPlane N) :
    ‖planeL2 N (derivativePlane N z)‖ ^ 2 =
      ∫ x : PhysicalCircle,
        ‖planeField N (derivativePlane N z) x‖ ^ 2 ∂spatialMeasure := by
  rw [planeL2_norm_sq, plane_mass_integral_eq_sum]

end NlsGge.HierarchyRiccati
