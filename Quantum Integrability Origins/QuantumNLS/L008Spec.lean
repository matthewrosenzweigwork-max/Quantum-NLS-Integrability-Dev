import QuantumNLS.Local008ModulusR29a
/-! integrator-authored trusted spec for LOCAL-008 cor:reset-exact-modulus-map (terra_review r205 PASS): headline statement(s) copied verbatim from Local008ModulusR29a (QuantumNLS.Local008ModulusR29a). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Metric Set BoundedContinuousFunction
namespace QuantumNLS.L008Spec
open QuantumNLS.Local008ModulusR29a
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Final (gcoef Pkg)
open QuantumNLS.Local007Statement (Fmap)
open QuantumNLS.Local006.CollectiveF (Seq scalarG)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem reset_exact_modulus_map_spec (hκ : 0 < κ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ (rr : L2T L → (ℤ →ᵇ ℝ)) (Z : L2T L → Seq),
        AnalyticOnNhd ℝ rr (ball (0 : L2T L) ρ) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, 1 / 2 < rr u n ∧ rr u n < 3 / 2) ∧
        AnalyticOnNhd ℝ Z (ball (0 : L2T L) ρ) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          Z u n = scalarG L κ (Real.pi / L) u n * (Real.sqrt (rr u n) : ℂ)) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          ‖Z u n‖ ^ 2 = (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ‖Z u‖ = ‖u‖) ∧
        (∀ u ∈ ball (0 : L2T L) ρ,
          ‖fderiv ℝ Z u - Fmap‖ ≤ C * ‖u‖ ^ 2) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          scalarG L κ (Real.pi / L) u n = 0 → Z u n = 0) := by
  exact QuantumNLS.Local008ModulusR29a.reset_exact_modulus_map hκ

end QuantumNLS.L008Spec
#print axioms QuantumNLS.L008Spec.reset_exact_modulus_map_spec
