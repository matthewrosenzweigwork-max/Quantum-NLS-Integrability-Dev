import Mathlib
import NlsGge.Definitions.PilotInterfaces

/- G6SUP_SEP PRODUCTION01 (target NlsGge/Atomic/G6/G6SupSeparable.lean, module NlsGge.Atomic.G6.G6SupSeparable). SUPPORTING, closes no packet.
   PhysicalL2 = Lp C 2 (haar probability on AddCircle 1) is separable; route: countably generated circle, probability
   (hence SFinite) Haar measure, Mathlib Lp.SecondCountableTopology. Stated as a theorem, NOT a global instance;
   consumers use `haveI := NlsGge.Atomic.G6Sup.physicalL2_separable`. -/
set_option autoImplicit false
open NlsGge.Pilot

namespace NlsGge.Atomic.G6Sup
noncomputable section

theorem physicalL2_separable : TopologicalSpace.SeparableSpace PhysicalL2 := by
  haveI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  haveI : MeasureTheory.IsProbabilityMeasure spatialMeasure := by
    unfold spatialMeasure; infer_instance
  haveI : MeasureTheory.SFinite spatialMeasure := inferInstance
  haveI : MeasurableSpace.CountablyGenerated PhysicalCircle := inferInstance
  haveI : MeasureTheory.IsSeparable spatialMeasure := inferInstance
  haveI : SecondCountableTopology PhysicalL2 := MeasureTheory.Lp.SecondCountableTopology
  exact inferInstance

end
end NlsGge.Atomic.G6Sup
