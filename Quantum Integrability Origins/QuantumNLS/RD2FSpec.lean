import QuantumNLS.UniformStaticR49b
/-! integrator-authored trusted spec for R-D2F4CE8F thm:uniform-static (selected Q06 witnesses, unconditional): headline statement(s) copied verbatim from UniformStaticR49b (QuantumNLS.UniformStaticR49b). -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open Set Filter Topology
open scoped ComplexConjugate Classical
namespace QuantumNLS.RD2FSpec
open QuantumNLS.UniformStaticR49b
open PhysicalTensor BetheCoefficientTransform Occupation OccupationHilbert FullOccupationAffinity FiniteCellGauge
open RetargetAnglesR48b RetargetStageR48b RetargetWeightsR48b RetargetCellR48b
open RetargetRoughR48b RetargetSelectionR49b RetargetPhysicalR48b RetargetBallR49b
variable {L κ : ℝ} [Fact (0 < L)]
open BetheLabels BetheCoefficientTransform in
open BetheLabels in
variable {X P : Type*}

set_option maxHeartbeats 8000000 in
theorem selected_uniform_static_spec (hκ : 0 < κ) :
    UniformStatic (L := L) hκ (particleStage (L := L) hκ) (sectorGauge (L := L) hκ) := by
  first
  | exact QuantumNLS.UniformStaticR49b.selected_uniform_static
  | (apply QuantumNLS.UniformStaticR49b.selected_uniform_static <;> assumption)

end QuantumNLS.RD2FSpec
#print axioms QuantumNLS.RD2FSpec.selected_uniform_static_spec
