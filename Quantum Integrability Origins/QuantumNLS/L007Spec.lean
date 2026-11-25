import QuantumNLS.Local007Statement
/-! integrator-authored trusted spec for LOCAL-007 prop:reset-exact-factor (review record r44 PASS): headline statement(s) copied verbatim from Local007Statement (QuantumNLS.Local007Statement). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Set Metric Filter Topology BoundedContinuousFunction
namespace QuantumNLS.L007Spec
open QuantumNLS.Local007Statement
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Final (gcoef Pkg)
open QuantumNLS.Local007Mul (mulCLM Seq)
variable {L κ r : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem reset_exact_factor_spec (hκ : 0 < κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
        (∀ n, Pkg L κ r ρ C n (a n) (b n)) ∧ AnalyticOnNhd ℝ rr (ball (0 : L2T L) ρ) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          (QuantumNLS.RootIndexedMasses.masses hκ u).1 n = ‖gcoef L κ * b n u‖ ^ 2 * rr u n) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, 1 / 2 < rr u n ∧ rr u n < 3 / 2) ∧ rr 0 = 1 ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ‖rr u - 1‖ ≤ C * ‖u‖ ^ 2) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ‖fderiv ℝ rr u‖ ≤ C * ‖u‖) ∧
        (∀ (G : L2T L → lp (fun _ : ℤ => ℂ) 2) (Cg : ℝ), 0 ≤ Cg →
          (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = gcoef L κ * b n u) →
          AnalyticOnNhd ℝ G (ball (0 : L2T L) ρ) →
          (∀ u ∈ ball (0 : L2T L) ρ, ‖fderiv ℝ G u - Fmap‖ ≤ Cg * ‖u‖ ^ 2) →
          ∃ (Z : L2T L → lp (fun _ : ℤ => ℂ) 2) (Cz : ℝ), 0 ≤ Cz ∧
            (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
              Z u n = gcoef L κ * b n u * ((Real.sqrt (rr u n) : ℝ) : ℂ)) ∧
            AnalyticOnNhd ℝ Z (ball (0 : L2T L) ρ) ∧
            (∀ u ∈ ball (0 : L2T L) ρ, ‖fderiv ℝ Z u - Fmap‖ ≤ Cz * ‖u‖ ^ 2) ∧
            (∀ u ∈ ball (0 : L2T L) ρ, ‖Z u‖ ^ 2 = ‖u‖ ^ 2)) := by
  exact QuantumNLS.Local007Statement.reset_exact_factor hκ hr hr2

end QuantumNLS.L007Spec
#print axioms QuantumNLS.L007Spec.reset_exact_factor_spec
