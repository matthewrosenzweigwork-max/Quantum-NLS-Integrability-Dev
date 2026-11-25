import QuantumNLS.Ext025GP04FlowR30m
import QuantumNLS.Ext025GP04AuditR30m
/-! integrator-authored trusted spec for EXT-025 GP-04 (owner continuous-D_x f condition; C1 clause verbatim): headline statement(s) copied verbatim from Ext025GP04FlowR30m (QuantumNLS.Ext025GP04FlowR30m). -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Filter Topology Function ODE
open scoped NNReal
namespace QuantumNLS.X25GP04Spec
open QuantumNLS.Ext025GP04FlowR30m
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : ℝ → E → E} {a b : ℝ} {s : Icc a b} {p : E} {R r L K : ℝ≥0}

set_option maxHeartbeats 8000000 in
theorem local_c1_spec (hf : IsPicardLindelof f s p R r L K)
    (A : ℝ → E → E →L[ℝ] E)
    (hd : ∀ t ∈ Icc a b, ∀ z ∈ closedBall p R, HasFDerivAt (f t) (A t z) z)
    (hA : ContinuousOn (uncurry A) (Icc a b ×ˢ closedBall p R))
    (hK : ∀ t ∈ Icc a b, ∀ z ∈ closedBall p R, ‖A t z‖ ≤ K)
    (hshort : 2 * (K : ℝ) * max (b - s) (s - a) ≤ 1) :
    ∃ φ : ℝ → E → E, ∃ J : E → ℝ → E →L[ℝ] E,
      (∀ x ∈ ball p r, Continuous (fun t => φ t x) ∧ φ s x = x ∧
        (∀ t ∈ Icc a b, φ t x ∈ closedBall p R ∧
          φ t x = picard f s x (fun z => φ z x) t ∧
          HasDerivWithinAt (fun z => φ z x) (f t (φ t x)) (Icc a b) t)) ∧
      (∀ x ∈ ball p r, Continuous (J x) ∧ J x s = ContinuousLinearMap.id ℝ E ∧
        (∀ t ∈ Icc a b, J x t = ContinuousLinearMap.id ℝ E +
          ∫ z in (s : ℝ)..t, (A z (φ z x)).comp (J x z)) ∧
        (∀ t ∈ Icc a b, HasDerivWithinAt (J x)
          ((A t (φ t x)).comp (J x t)) (Icc a b) t ∧ HasFDerivAt (φ t) (J x t) x)) ∧
      (∀ t ∈ Icc a b, ContDiffOn ℝ 1 (φ t) (ball p r)) := by
  first
  | exact QuantumNLS.Ext025GP04FlowR30m.local_c1
  | (apply QuantumNLS.Ext025GP04FlowR30m.local_c1 <;> assumption)

set_option maxHeartbeats 8000000 in
theorem local_c1_from_contract_spec (hf : IsPicardLindelof f s p R r L K)
    (A : ℝ → E → E →L[ℝ] E)
    (hd : ∀ t ∈ Icc a b, ∀ z ∈ closedBall p R, HasFDerivAt (f t) (A t z) z)
    (hA : ContinuousOn (uncurry A) (Icc a b ×ˢ closedBall p R))
    (hK : ∀ t ∈ Icc a b, ∀ z ∈ closedBall p R, ‖A t z‖ ≤ K)
    (hshort : 2 * (K : ℝ) * max (b - s) (s - a) ≤ 1) :
    ∃ φ : ℝ → E → E, ∃ J : E → ℝ → E →L[ℝ] E,
      (∀ x ∈ ball p r, Continuous (fun t => φ t x) ∧ φ s x = x ∧
        (∀ t ∈ Icc a b, φ t x ∈ closedBall p R ∧
          φ t x = picard f s x (fun z => φ z x) t ∧
          HasDerivWithinAt (fun z => φ z x) (f t (φ t x)) (Icc a b) t)) ∧
      (∀ x ∈ ball p r, Continuous (J x) ∧ J x s = ContinuousLinearMap.id ℝ E ∧
        (∀ t ∈ Icc a b, J x t = ContinuousLinearMap.id ℝ E +
          ∫ z in (s : ℝ)..t, (A z (φ z x)).comp (J x z)) ∧
        (∀ t ∈ Icc a b, HasDerivWithinAt (J x)
          ((A t (φ t x)).comp (J x t)) (Icc a b) t ∧ HasFDerivAt (φ t) (J x t) x)) ∧
      (∀ t ∈ Icc a b, ContDiffOn ℝ 1 (φ t) (ball p r)) := by
  exact (QuantumNLS.Ext025GP04ContractR30m.contract_GP04.{_, 0}).continuouslyDifferentiableFlow hf A hd hA hK hshort

end QuantumNLS.X25GP04Spec

namespace QuantumNLS.X25GP04ContractPin
open QuantumNLS.Ext025GP04ContractR30m
universe u v
theorem contract_GP04_spec : QuantumNLS.Ext025GP04ContractR30m.Contract.{u,v} :=
  QuantumNLS.Ext025GP04ContractR30m.contract_GP04.{u,v}
end QuantumNLS.X25GP04ContractPin
#print axioms QuantumNLS.X25GP04ContractPin.contract_GP04_spec
#print axioms QuantumNLS.X25GP04Spec.local_c1_spec
#print axioms QuantumNLS.X25GP04Spec.local_c1_from_contract_spec
