import NlsGge.Sobolev.PeriodicBridge

/-! The physical L2 space carries the Borel sigma algebra of its actual norm topology. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot

/-- Canonical measurable structure for physical L2 field laws. -/
instance physicalL2MeasurableSpace : MeasurableSpace PhysicalL2 := borel PhysicalL2

/-- This measurable structure is precisely the Borel sigma algebra of the L2 topology. -/
instance physicalL2BorelSpace : BorelSpace PhysicalL2 := ⟨rfl⟩

end NlsGge.Pilot
