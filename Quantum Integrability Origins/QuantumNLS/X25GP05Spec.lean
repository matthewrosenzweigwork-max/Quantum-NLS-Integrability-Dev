import QuantumNLS.Ext025LGP05Wrapper
/-! integrator-authored trusted spec for EXT-025 contract_GP05_full2 (contract ACCEPT): headline statement(s) copied verbatim from Ext025LGP05Wrapper (QuantumNLS.Ext025L). -/
set_option autoImplicit false
universe u v w
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Topology Metric MeasureTheory
open scoped ENNReal NNReal
namespace QuantumNLS.X25GP05Spec
open QuantumNLS.Ext025L
variable {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {T : Type w} [MeasurableSpace T]
variable {μ : Measure T} {α : E → T → StrongDual ℂ X} {U : Set E} {b : T → ℝ}

set_option maxHeartbeats 8000000 in
theorem contract_GP05_full2_spec :
    GP05_one.{v} ∧ GP05_banach.{u} ∧ GP05_limit.{u} ∧ GP05_sum.{u} ∧ GP05_series_bounds.{u} ∧
      GP05_int.{v, w} ∧ GP05_int_banach.{u, w} ∧ GP05_wrapper.{u, w} := by
  exact QuantumNLS.Ext025L.contract_GP05_full2 

end QuantumNLS.X25GP05Spec
#print axioms QuantumNLS.X25GP05Spec.contract_GP05_full2_spec
