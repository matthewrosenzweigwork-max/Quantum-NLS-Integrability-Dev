import NlsGge.Sobolev.PhysicalWeighted

/-! Canonical norm-Borel structures for the actual source weighted carriers. -/
set_option autoImplicit false
noncomputable section
namespace NlsGge.Pilot

instance fullWeightedMeasurableSpace {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    MeasurableSpace (FullWeightedHilbert c s) := borel (FullWeightedHilbert c s)

instance fullWeightedBorelSpace {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    BorelSpace (FullWeightedHilbert c s) := ⟨rfl⟩

instance physicalWeightedMeasurableSpace {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    MeasurableSpace (PhysicalWeighted c s) := borel (PhysicalWeighted c s)

instance physicalWeightedBorelSpace {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    BorelSpace (PhysicalWeighted c s) := ⟨rfl⟩

end NlsGge.Pilot
