import QuantumNLS.RB01Main
/-! integrator-authored trusted spec for R-EC25334D thm:global-B01-actions (review record r40 PASS): headline statement(s) copied verbatim from RB01Main (QuantumNLS.RB01Main). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal NNReal InnerProductSpace
namespace QuantumNLS.REC2Spec
open QuantumNLS.RB01Main
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ProductTorusComplexification (Cx)
open QuantumNLS.TerraMultiRound30HessianBridge (Actions)
open QuantumNLS.TerraMultiRound31CoordinateHessian (actionCoordinate coordinate_analytic)
open QuantumNLS.TerraMultiRound31FiniteActions (finiteActions finiteActions_analytic)
open QuantumNLS.RB01Head (trunc trunc_apply)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem global_B01_actions_spec (hκ : 0 < κ) (u₀ : L2T L) :
    (∃ U : Set (L2T L), IsOpen U ∧ u₀ ∈ U ∧ AnalyticOnNhd ℝ (Actions hκ) U ∧
      ∃ N : ℕ, ∃ g : L2T L → lp (fun _ : ℤ => ℂ) 2, ∃ r : L2T L → lp (fun _ : ℤ => ℂ) ∞,
        AnalyticOnNhd ℝ g U ∧ AnalyticOnNhd ℝ r U ∧
        (∀ u ∈ U, ∀ n : ℤ, ¬ (N : ℝ) < |(n : ℝ)| → g u n = 0 ∧ r u n = 0) ∧
        (∀ u ∈ U, ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
          Actions hκ u n = ‖g u n‖ ^ 2 * (r u n).re ∧ (r u n).im = 0 ∧ 1 / 2 < (r u n).re ∧
            (r u n).re < 3 / 2) ∧
        (∃ R > (0 : ℝ), ball u₀ R ⊆ U ∧ ∃ M : ℝ, ∃ gc : Cx (L2T L) → lp (fun _ : ℤ => ℂ) 2,
          ∃ rc : Cx (L2T L) → lp (fun _ : ℤ => ℂ) ∞, ∃ Ic : ℤ → Cx (L2T L) → ℂ,
          AnalyticOnNhd ℂ gc (ball (Cx.ι u₀) R) ∧ AnalyticOnNhd ℂ rc (ball (Cx.ι u₀) R) ∧
          (∀ z ∈ ball (Cx.ι u₀) R, ‖gc z‖ ≤ M ∧ ‖rc z‖ ≤ M) ∧
          (∀ x ∈ ball u₀ R, gc (Cx.ι x) = g x ∧ rc (Cx.ι x) = r x) ∧
          ∀ n : ℤ, ¬ (N : ℝ) < |(n : ℝ)| → AnalyticOnNhd ℂ (Ic n) (ball (Cx.ι u₀) R) ∧
            (∀ z ∈ ball (Cx.ι u₀) R, ‖Ic n z‖ ≤ M) ∧
            ∀ x ∈ ball u₀ R, Ic n (Cx.ι x) = ((Actions hκ x n : ℝ) : ℂ))) ∧
    (∀ u : L2T L, IsCompactOperator (fderiv ℝ (Actions hκ) u)) ∧
    (∀ (S : Finset ℤ) (T : L2T L →L[ℝ] L2T L →L[ℝ] lp (fun _ : ℤ => ℝ) 1),
      (∀ k, k ∉ S → T (QuantumNLS.Fourier.modeLp L k) (QuantumNLS.Fourier.modeLp L k) k =
        fderiv ℝ (fderiv ℝ (Actions hκ)) 0 (QuantumNLS.Fourier.modeLp L k) (QuantumNLS.Fourier.modeLp L k) k) →
      2 ≤ ‖T‖) := by
  exact QuantumNLS.RB01Main.global_B01_actions hκ u₀

end QuantumNLS.REC2Spec
#print axioms QuantumNLS.REC2Spec.global_B01_actions_spec
