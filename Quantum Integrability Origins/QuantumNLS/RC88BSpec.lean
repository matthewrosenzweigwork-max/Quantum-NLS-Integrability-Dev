import QuantumNLS.VarFinal
/-! integrator-authored trusted spec for R-C88B5D59 CC:F04:variable-coupling, energy-gap limit (review record r21 FULL ACCEPT): headline statement(s) copied verbatim from VarFinal (QuantumNLS.VarFinal). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace QuantumNLS.RC88BSpec
open QuantumNLS.VarFinal
open QuantumNLS.BetheLabels QuantumNLS.F02FiniteGap QuantumNLS.AdjacentResponse QuantumNLS.BetheRoots
open QuantumNLS.F04SelSetup QuantumNLS.F04SelBand QuantumNLS.LocalHeight QuantumNLS.DetGapRowLim
open QuantumNLS.VarCoupling QuantumNLS.VarMain QuantumNLS.VarW2Weak
open QuantumNLS.BulkResponseForm (L2Unit BulkResponseData BulkMeasure)
open QuantumNLS.QuantileForm (uI)
open QuantumNLS.QuantileTransport (qm empirical W2)
open QuantumNLS.StepIntegrals (stepL2)
open QuantumNLS.StrongLimitBulk (Q2)
open PhysicalTensor (L2T)

set_option maxHeartbeats 8000000 in
theorem variable_coupling_spec {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L)
    (hu : ‖u‖ = 1) (hbulk : BulkMeasure (Mu hκ u))
    {κs : ℕ → ℝ} (hκs : Tendsto κs atTop (𝓝 κ)) {κm κp : ℝ} (hκm : 0 < κm)
    (hbd : ∀ᶠ N : ℕ in atTop, κm ≤ κs N ∧ κs N ≤ κp)
    {b a : ℤ} (hab : b < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0))
    (hW2 : Tendsto (fun n : ℕ => W2 (empirical (n + 1) (arrRoots L (κs n / ((n : ℝ) + 1)) (η n)))
        (Mu hκ u)) atTop (𝓝 0) ∨
      Tendsto (fun n : ℕ => W2 (empirical (n + 1)
        (arrRoots L (κs n / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a))) (Mu hκ u)) atTop (𝓝 0))
    {F : L2Unit} (hF : (⟨L, κ, Fact.out, hκ, Mu hκ u, hbulk⟩ : BulkResponseData).IsResponse F)
    {f : ℝ → ℝ} (hfm : Measurable f) (hFf : (F : ℝ → ℝ) =ᵐ[uI] fun t => f (qm (Mu hκ u) t))
    (xl : ℝ → ℝ)
    (hxl : ∀ k : ℤ, b ≤ k → k < a → ∀ lam : ℝ, (k : ℝ) < lam → lam < (k : ℝ) + 1 →
      th hκ u (xl lam) = lam * Real.pi) :
    IntervalIntegrable (fun lam => fext L κ (Mu hκ u) f (xl lam)) volume (b : ℝ) a ∧
    Tendsto (fun n : ℕ => ∑ i, arrRoots L (κs n / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a) i ^ 2 -
        ∑ i, arrRoots L (κs n / ((n : ℝ) + 1)) (η n) i ^ 2) atTop
      (𝓝 (4 * Real.pi * ∫ lam in (b : ℝ)..(a : ℝ), fext L κ (Mu hκ u) f (xl lam))) := by
  exact QuantumNLS.VarFinal.variable_coupling hκ u hu hbulk hκs hκm hbd hab hb ha η hηb hη hW2 hF hfm hFf xl hxl

end QuantumNLS.RC88BSpec
#print axioms QuantumNLS.RC88BSpec.variable_coupling_spec
