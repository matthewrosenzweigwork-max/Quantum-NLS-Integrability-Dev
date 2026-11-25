import QuantumNLS.F03Actual
/-! integrator-authored trusted spec for R-BB7EDFF3 CC:F03:actual (terra_review r192 PASS): headline statement(s) copied verbatim from F03Actual (QuantumNLS.F03Actual). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace QuantumNLS.RBB7Spec
open QuantumNLS.F03Actual
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.BornConvergence (TendstoInProbability)
open QuantumNLS.BulkResponseActual (ActualBulkData empiricalProb)
open QuantumNLS.BulkResponseForm (L2Unit)
open QuantumNLS.StepIntegrals (stepL2 norm_sq_step)
open QuantumNLS.StrongLimitBulk (Q2)
open QuantumNLS.GaudinResponse (responseVec)
open QuantumNLS.ProductEnergyPreparation (OneH1)
open QuantumNLS.ChargeEnergy (energyH1)
open QuantumNLS.RootEnergyMomentLaws (law sample_second_moment)
open QuantumNLS.RootEnergyMomentExpectation (sampleEnergy)
open QuantumNLS.QuantileTransport (W2 HasFiniteSecondMoment empirical)
open QuantumNLS.EmpiricalRapidity (empiricalMeasure)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem actual_mean_square_convergence_spec (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) :
    ∃ D : ActualBulkData L κ hκ u hu, ∃ F : L2Unit,
      D.toBulkResponseData.IsResponse F ∧
      (∀ F' : L2Unit, D.toBulkResponseData.IsResponse F' → F' = F) ∧
      Tendsto (fun N : ℕ => ∫⁻ m, ENNReal.ofReal
          (‖stepL2 (arrRoots L (κ / N) m) - Q2 D.toBulkResponseData‖ ^ 2) ∂(law hκ u hu N))
        atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => ∫⁻ m, ENNReal.ofReal
          (‖stepL2 (responseVec L (κ / N) (arrRoots L (κ / N) m)) - F‖ ^ 2) ∂(law hκ u hu N))
        atTop (𝓝 0) := by
  exact QuantumNLS.F03Actual.actual_mean_square_convergence hκ u hu hH

end QuantumNLS.RBB7Spec
#print axioms QuantumNLS.RBB7Spec.actual_mean_square_convergence_spec
