import QuantumNLS.Local002Bridge
/-! integrator-authored trusted spec for LOCAL-002 lem:reset-analytic-projections (terra_review r182 FULL): headline statement(s) copied verbatim from Local002Bridge (QuantumNLS.Local002Bridge). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.L002Spec
open QuantumNLS.Local002Bridge
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.PhysicalTensor
variable {L κ : ℝ}

set_option maxHeartbeats 8000000 in
theorem reset_analytic_projections_profile_spec [Fact (0 < L)] (hL : 0 < L) {r : ℝ}
    (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ n : ℤ,
      (∀ u : L2T L, ‖u‖ < ρ →
        IsSelfAdjointGraph (LuGraph L κ (circleRep u) (parity n)) ∧
        (∀ z : ℂ, ‖z - (pm L n : ℂ)‖ = r →
          ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (circleRep u) (parity n) z R) ∧
        Module.finrank ℂ (LinearMap.range
          (perturbedProj L κ (circleRep u) n r : H2 L →ₗ[ℂ] H2 L)) = 2 ∧
        ‖perturbedProj L κ (circleRep u) n r - freeProj L κ n r‖ ≤ C * ‖u‖) ∧
      AnalyticOnNhd ℝ (fun u : L2T L => perturbedProj L κ (circleRep u) n r) (ball 0 ρ) := by
  exact QuantumNLS.Local002Bridge.reset_analytic_projections_profile hL hr hr2

end QuantumNLS.L002Spec
#print axioms QuantumNLS.L002Spec.reset_analytic_projections_profile_spec
