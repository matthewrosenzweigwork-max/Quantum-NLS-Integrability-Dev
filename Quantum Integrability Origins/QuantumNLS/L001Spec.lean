import QuantumNLS.Local001FinalB
/-! integrator-authored trusted spec for LOCAL-001 lem:reset-free-resolvent (Terra r176 FULL ACCEPT): headline statement(s) copied verbatim from Local001FinalB (QuantumNLS.ResetFreeResolventLOCAL001). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace QuantumNLS.L001Spec
open QuantumNLS.ResetFreeResolventLOCAL001
open CompletionB

set_option maxHeartbeats 8000000 in
theorem reset_free_resolvent_estimates_spec {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hL : 0 < L) (hκ : 0 < κ) (n : ℤ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) :
    ‖LocalSpectral.resolvent L κ (fun _ => 0) (LocalSpectral.parity n) z‖ ≤ r⁻¹ ∧
    (∀ f : VectorInterval L, ∀ᵐ x ∂(LocalSpectral.μI L),
      ‖LocalSpectral.resolvent L κ (fun _ => 0) (LocalSpectral.parity n) z f x‖ ≤
        resolventConstant L r * ‖f‖) ∧
    resolventConstant L r ^ 2 = L⁻¹ *
      (r⁻¹ ^ 2 + 2 * ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2) ∧
    ‖potentialResolvent κ hκ.le hL n hr hsmall hz u‖ ≤
      2 * Real.sqrt κ * resolventConstant L r * ‖u‖ := by
  exact QuantumNLS.ResetFreeResolventLOCAL001.reset_free_resolvent_estimates κ hL hκ n hr hsmall hz u

end QuantumNLS.L001Spec
#print axioms QuantumNLS.L001Spec.reset_free_resolvent_estimates_spec
