import QuantumNLS.Local006FinalJ
/-! integrator-authored trusted spec for LOCAL-006 thm:reset-collective-spectral (review record r45 PASS): headline statement(s) copied verbatim from Local006FinalJ (QuantumNLS.Local006.FinalJ). -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal
namespace QuantumNLS.L006Spec
open QuantumNLS.Local006
open QuantumNLS.Local006.FinalJ
open QuantumNLS.PhysicalTensor QuantumNLS.Local002Bridge QuantumNLS.Local005
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SolidMajorantH QuantumNLS.Local006.PhysicalRegroupI
  QuantumNLS.Local006.TaylorBindingI QuantumNLS.Local006.NormalizedDerivativeJ
  QuantumNLS.Local006.ChartKernelJ QuantumNLS.Local006.CollectiveF
  QuantumNLS.Local006.FirstJetF QuantumNLS.Local006.G3Fourier
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
variable {L r κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem reset_collective_spectral_spec (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ (G : L2T L → Seq)
      (p : FormalMultilinearSeries ℝ (L2T L) Seq)
      (e : OpenPartialHomeomorph (L2T L) Seq),
      AnalyticOnNhd ℝ G (ball 0 ρ) ∧ HasFPowerSeriesAt G p 0 ∧
      (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = scalarG L κ r u n) ∧
      G 0 = 0 ∧ fderiv ℝ G 0 =
        (QuantumNLS.Local006.FirstJetF.fourierR L : L2T L →L[ℝ] Seq) ∧
      (e : L2T L → Seq) = G ∧ (0 : L2T L) ∈ e.source ∧ (0 : Seq) ∈ e.target ∧
      e.symm 0 = 0 ∧ AnalyticAt ℝ (e.symm : Seq → L2T L) 0 ∧
      (∀ k : ℕ, Even k → ∀ u : L2T L, p k (fun _ => u) = 0) ∧
      (∀ u ∈ ball (0 : L2T L) ρ,
        ‖G u - QuantumNLS.Local006.FirstJetF.fourierR L u - p 3 (fun _ => u)‖ ≤ C * ‖u‖ ^ 5) ∧
      (∀ u ∈ ball (0 : L2T L) ρ,
        ‖fderiv ℝ G u - (QuantumNLS.Local006.FirstJetF.fourierR L : L2T L →L[ℝ] Seq)‖ ≤
          C * ‖u‖ ^ 2) ∧
      (∀ (u : L2T L) (n : ℤ),
        p 3 (fun _ => u) n = printedG3 L κ (fun m => QuantumNLS.Fourier.fourierL2 L u m) n) ∧
      (∀ (u : L2T L) (n : ℤ),
        Summable (fun ab : ℤ × ℤ =>
          ‖doubleTerm L (fun m => QuantumNLS.Fourier.fourierL2 L u m) n ab‖) ∧
        Summable (fun a : ℤ =>
          ‖normTerm L (fun m => QuantumNLS.Fourier.fourierL2 L u m) n a‖)) ∧
      (∀ u ∈ ball (0 : L2T L) ρ, TaylorClauses hL hκ hr hs G p u ∧ KernelClauses hL hκ hr hs G u) := by
  exact QuantumNLS.Local006.FinalJ.reset_collective_spectral hL hκ hr hs

end QuantumNLS.L006Spec
#print axioms QuantumNLS.L006Spec.reset_collective_spectral_spec
