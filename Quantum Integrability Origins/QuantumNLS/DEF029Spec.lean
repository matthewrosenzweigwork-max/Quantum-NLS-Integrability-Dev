import QuantumNLS.PhysicalAuxiliaryDensity
/-! integrator-authored trusted spec for DEF-029 Auxiliary one-body density and common-phase ray (Terra r137 REALIZED for the physical family): frozen statements restated verbatim. -/
namespace DEF029Spec
open scoped InnerProductSpace ComplexConjugate ComplexOrder
open Filter Topology
open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.AuxiliaryDensity
open QuantumNLS.BetheOccupationGauge (UniversalSelection Gauge)
open QuantumNLS.BetheCoefficientTransform (BetheBasis HN)
open QuantumNLS.CartesianOccupationTransfer (coordinates physical)
open QuantumNLS.ExactDensity (Gamma)
open QuantumNLS QuantumNLS.PhysicalAuxiliaryDensity

set_option maxHeartbeats 4000000 in
theorem PhysicalPreparation_gammaOp_isAuxiliaryOperator_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} {hκ : 0 < κ} (P : PhysicalPreparation L κ hκ) (q : ℕ) :
    IsAuxiliaryOperator (P.gammaOp q) (P.gammaEntry q) := by
  apply QuantumNLS.PhysicalAuxiliaryDensity.PhysicalPreparation.gammaOp_isAuxiliaryOperator <;> assumption

set_option maxHeartbeats 4000000 in
theorem PhysicalPreparation_gammaOp_isPositive_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} {hκ : 0 < κ} (P : PhysicalPreparation L κ hκ) (q : ℕ) :
    (P.gammaOp q).IsPositive := by
  apply QuantumNLS.PhysicalAuxiliaryDensity.PhysicalPreparation.gammaOp_isPositive <;> assumption

set_option maxHeartbeats 4000000 in
theorem PhysicalPreparation_gammaOp_posTrace_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} {hκ : 0 < κ} (P : PhysicalPreparation L κ hκ) (q : ℕ) :
    QuantumNLS.TraceClass.posTrace (P.gammaOp q) = 1 := by
  apply QuantumNLS.PhysicalAuxiliaryDensity.PhysicalPreparation.gammaOp_posTrace <;> assumption

set_option maxHeartbeats 4000000 in
theorem PhysicalPreparation_gammaOp_isTraceClass_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} {hκ : 0 < κ} (P : PhysicalPreparation L κ hκ) (q : ℕ) :
    QuantumNLS.TraceClass.IsTraceClass (P.gammaOp q) := by
  apply QuantumNLS.PhysicalAuxiliaryDensity.PhysicalPreparation.gammaOp_isTraceClass <;> assumption

set_option maxHeartbeats 4000000 in
theorem PhysicalPreparation_auxiliary_operator_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} {hκ : 0 < κ} (P : PhysicalPreparation L κ hκ) (q : ℕ) :
    IsAuxiliaryOperator (P.gammaOp q) (P.gammaEntry q) ∧ (P.gammaOp q).IsPositive ∧
      QuantumNLS.TraceClass.IsTraceClass (P.gammaOp q) ∧
      QuantumNLS.TraceClass.posTrace (P.gammaOp q) = 1 := by
  apply QuantumNLS.PhysicalAuxiliaryDensity.PhysicalPreparation.auxiliary_operator <;> assumption

set_option maxHeartbeats 4000000 in
theorem PhysicalPreparation_tendsto_column_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} {hκ : 0 < κ} (P : PhysicalPreparation L κ hκ) (w : OneParticle) (hw : ‖w‖ = 1)
    (b : ℤ) (hb : w b ≠ 0) (hlim : HasRankOneLimit (fun q => P.gammaOp q) w) :
    Tendsto (fun q => normalizedColumn (P.gammaOp q) b) atTop
      (𝓝 ((conj (w b) / ((‖w b‖ : ℝ) : ℂ)) • w)) := by
  apply QuantumNLS.PhysicalAuxiliaryDensity.PhysicalPreparation.tendsto_column <;> assumption

end DEF029Spec
#print axioms DEF029Spec.PhysicalPreparation_gammaOp_isAuxiliaryOperator_spec
#print axioms DEF029Spec.PhysicalPreparation_gammaOp_isPositive_spec
#print axioms DEF029Spec.PhysicalPreparation_gammaOp_posTrace_spec
#print axioms DEF029Spec.PhysicalPreparation_gammaOp_isTraceClass_spec
#print axioms DEF029Spec.PhysicalPreparation_auxiliary_operator_spec
#print axioms DEF029Spec.PhysicalPreparation_tendsto_column_spec
