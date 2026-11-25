import QuantumNLS.Prop023FinalPhys
/-! integrator-authored trusted spec for PROP-023 Q7B:lem:moments (review record r22 FULL ACCEPT): headline statement(s) copied verbatim from Prop023FinalPhys (QuantumNLS.Prop023FinalPhys). -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace QuantumNLS.P023Spec
open QuantumNLS.Prop023FinalPhys
open Ext006NumberPhase Ext006PhysicalVacuum
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem prop023_spec (x : Ext025B3PhysicalSectors.Fock L) (hx : ‖x‖ = 1)
    (hq : Ext006PhysQuasifree.PhysicalQuasifreeSource x) {Q : ℝ} (hQ : 1 ≤ Q)
    (hN : numberExpectation (fun n => (n : ℝ≥0∞)) x ≤ ENNReal.ofReal (Q - 1)) :
    exponentialMoment Q x ≤ ENNReal.ofReal (Real.exp (1 / 4 : ℝ)) ∧
    ∀ j : ℕ, 1 ≤ j → ∃ hx' : x ∈ (polynomialRoot (L := L) j).domain,
      ‖polynomialRoot j ⟨x, hx'⟩‖ ≤ Real.rpow (32 * Q * j) ((j : ℝ) / 2) := by
  exact QuantumNLS.Prop023FinalPhys.prop023 x hx hq hQ hN

end QuantumNLS.P023Spec
#print axioms QuantumNLS.P023Spec.prop023_spec
