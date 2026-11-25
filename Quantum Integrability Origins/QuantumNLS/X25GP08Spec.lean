import QuantumNLS.Ext025GP08R27m
/-! integrator-authored trusted spec for EXT-025 contract_GP08_fixed (contract ACCEPT): headline statement(s) copied verbatim from Ext025GP08R27m (QuantumNLS.Ext025GP08R27m). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology Function
open scoped ENNReal InnerProductSpace
namespace QuantumNLS.X25GP08Spec
open QuantumNLS.Ext025GP08R27m
open BetheChargeResolution Ext025B6PVM Ext025B8SimpleCalculus Ext025B8BorelCalculus
open Ext025B9MaximalIntegral Ext025B9IntegralDomain Ext025B9IntegralCutoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 8000000 in
theorem contract_GP08_fixed_spec (P : ProjectionMeasure E) :
    (∀ f hf, IsSelfAdjoint (operator (mapped P f hf) (fun t => (t : ℂ))
      Complex.measurable_ofReal) ∧
      (∀ x, x ∈ (operator (mapped P f hf) (fun t => (t : ℂ)) Complex.measurable_ofReal).domain ↔
        x ∈ (operator P (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf)).domain) ∧
      (∀ x hx, operator (mapped P f hf) (fun t => (t : ℂ)) Complex.measurable_ofReal
          ⟨x,(domain_mapped P f hf x).mpr hx⟩ =
        operator P (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf) ⟨x,hx⟩)) ∧
    (∀ f g hf hg s t, MeasurableSet s → MeasurableSet t →
      (mapped P f hf).toFun s * (mapped P g hg).toFun t =
        (mapped P g hg).toFun t * (mapped P f hf).toFun s) ∧
    OriginalContract P := by
  exact QuantumNLS.Ext025GP08R27m.contract_GP08_fixed P

end QuantumNLS.X25GP08Spec
#print axioms QuantumNLS.X25GP08Spec.contract_GP08_fixed_spec
