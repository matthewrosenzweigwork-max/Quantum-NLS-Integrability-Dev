import QuantumNLS.IndexedPeriodTheoremR30b
/-! integrator-authored trusted spec for LOCAL-016 reset:period-theorem (terra_review r209 FULL ACCEPT): headline statement(s) copied verbatim from IndexedPeriodTheoremR30b (QuantumNLS.IndexedPeriodTheoremR30b). -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Filter Topology Complex
open scoped InnerProductSpace
namespace QuantumNLS.L016Spec
open QuantumNLS.IndexedPeriodTheoremR30b
open PhysicalTensor IndexedUnitRayR30b IndexedGlobalR27b IndexedScalingR27b
  IndexedRegularityR28b IndexedSymplecticR28b RayPeriodUpgrade
attribute [local instance] InnerProductSpace.complexToReal
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem reset_period_theorem_spec (hκ : 0 < κ) :
    0 < delta L κ ∧ (delta L κ)^2 = (1/1000000000000 : ℝ)/(κ*L) ∧
    (∀ n : ℤ, ∀ u : L2T L, ‖u‖ < delta L κ → flow hκ n (2*Real.pi) u = u) ∧
    (∀ n : ℤ, ∀ t : ℝ, MapsTo (flow (L := L) hκ n t)
      (ball 0 (delta L κ)) (ball 0 (delta L κ))) := by
  exact QuantumNLS.IndexedPeriodTheoremR30b.reset_period_theorem hκ

end QuantumNLS.L016Spec
#print axioms QuantumNLS.L016Spec.reset_period_theorem_spec
