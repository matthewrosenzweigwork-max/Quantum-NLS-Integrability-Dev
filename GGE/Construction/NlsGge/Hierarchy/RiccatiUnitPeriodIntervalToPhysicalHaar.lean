import NlsGge.Hierarchy.RiccatiQ2PeriodicIntegration
import NlsGge.Definitions.PilotInterfaces
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati

open NlsGge.Pilot
open MeasureTheory

/-- On the actual period-one circle, an interval integral of a lifted function
is its integral against the normalized physical Haar probability measure. -/
theorem unitIntervalIntegral_lift_eq_spatialHaar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : PhysicalCircle → E) :
    (∫ t in (0 : ℝ)..1, f (t : PhysicalCircle)) =
      ∫ x : PhysicalCircle, f x ∂spatialMeasure := by
  calc
    (∫ t in (0 : ℝ)..1, f (t : PhysicalCircle)) =
        ∫ x : PhysicalCircle, f x := by
      simpa only [zero_add] using
        (AddCircle.intervalIntegral_preimage (1 : ℝ) 0 f)
    _ = ∫ x : PhysicalCircle, f x ∂spatialMeasure := by
      rw [spatialMeasure, AddCircle.integral_haarAddCircle]
      norm_num

end NlsGge.HierarchyRiccati
