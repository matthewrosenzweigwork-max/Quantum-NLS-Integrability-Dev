import QuantumNLS.RB7BindFinal
/-! integrator-authored trusted spec for R-7B122087 to HierarchyInputR25m binding: headline statement(s) copied verbatim from RB7BindFinal (QuantumNLS.RB7BindFinal). -/
set_option autoImplicit false
namespace QuantumNLS.RBindSpec
open QuantumNLS.RB7BindFinal
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem hierarchyInputR25m_unconditional_spec (hκ : 0 < κ) :
    QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ := by
  first
  | exact QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional
  | (apply QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional <;> assumption)

end QuantumNLS.RBindSpec

namespace QuantumNLS.RBindPins
open MeasureTheory Topology
open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow QuantumNLS.Def033HierarchyR24m
open QuantumNLS.Def024LowEquivariance QuantumNLS.Def033CoreR24m QuantumNLS.HierarchyInputR25m
theorem pin_HierarchyR7B122087Input (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) :
    QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ ↔
  ∀ w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K,
    QuantumNLS.REF88PrintedChart.PrintedChart hκ w →
    SobolevHomeomorphisms w → ScalarUniqueness (L := L) hκ →
    ScalarMomentIdentification (L := L) hκ →
    HierarchyConclusion (κ := κ) w (fun u n => (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := Iff.rfl
end QuantumNLS.RBindPins
#print axioms QuantumNLS.RBindPins.pin_HierarchyR7B122087Input
#print axioms QuantumNLS.RBindSpec.hierarchyInputR25m_unconditional_spec
