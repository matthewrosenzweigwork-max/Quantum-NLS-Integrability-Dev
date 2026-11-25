import QuantumNLS.DynamicGaugeFinalR35m
/-! integrator-authored trusted spec for R-8362E5EB prop:audit-dynamic-gauge (final): headline statement(s) copied verbatim from DynamicGaugeFinalR35m (QuantumNLS.DynamicGaugeFinalR35m). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
noncomputable section
open Filter Topology
open scoped Classical
namespace QuantumNLS.R836Spec
open QuantumNLS.DynamicGaugeFinalR35m
open Def033HierarchyR24m (Smooth physical)
open ReconstructionR33m (flows RD8362E5EBInput)
open UniformStaticR31m
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem audit_dynamic_gauge_spec (hκ : 0 < κ) :
    RD8362E5EBInput hκ (flows hκ (hierarchy (L := L) hκ)) (gauge (L := L) hκ) := by
  first
  | exact QuantumNLS.DynamicGaugeFinalR35m.audit_dynamic_gauge
  | (apply QuantumNLS.DynamicGaugeFinalR35m.audit_dynamic_gauge <;> assumption)

set_option maxHeartbeats 8000000 in
theorem dynamic_gauge_conclusion_spec (hκ : 0 < κ) :
    ∃ (j : ℕ → ℕ) (q : FullGauge),
      Monotone j ∧ Tendsto j atTop atTop ∧
      (∀ S > 0, UniformError (unitBall (L := L) S)
        (fun n _ => pairs (j n)) (cartesianError hκ q)) ∧
      (∀ S > 0, ∀ α > 0, ∀ ε > 0, ∀ᶠ n in atTop,
        ∀ u ∈ unitBall (L := L) S, ∀ p ∈ eligible hκ (j n) α u,
          phaseError hκ q n u p ≤ ε ∧ missingInitial hκ n u p ≤ ε ∧
          missingFinal hκ n u p ≤ ε ∧ affinityError hκ n u p ≤ ε ∧
          defectError hκ q n u p ≤ ε) ∧
      ExteriorExact ∧
      RD8362E5EBInput hκ (flows hκ (hierarchy (L := L) hκ))
        (DynamicGaugePhysicalR34m.physicalGauge q) := by
  first
  | exact QuantumNLS.DynamicGaugeFinalR35m.dynamic_gauge_conclusion
  | (apply QuantumNLS.DynamicGaugeFinalR35m.dynamic_gauge_conclusion <;> assumption)

end QuantumNLS.R836Spec
#print axioms QuantumNLS.R836Spec.audit_dynamic_gauge_spec
#print axioms QuantumNLS.R836Spec.dynamic_gauge_conclusion_spec
