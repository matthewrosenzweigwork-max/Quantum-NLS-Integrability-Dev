import QuantumNLS.DetGapFinal
/-! integrator-authored trusted spec for R-C455C541 CC:F04:deterministic-gap (review record r21 FULL ACCEPT): headline statement(s) copied verbatim from DetGapFinal (QuantumNLS.DetGapFinal). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace QuantumNLS.RC455Spec
open QuantumNLS.DetGapFinal
open QuantumNLS.BetheLabels QuantumNLS.F02FiniteGap QuantumNLS.AdjacentResponse QuantumNLS.BetheRoots
open QuantumNLS.F04SelSetup QuantumNLS.F04SelBand QuantumNLS.LocalHeight QuantumNLS.DetGapRowLim
open QuantumNLS.DetGapMain
open QuantumNLS.BulkResponseForm (L2Unit BulkResponseData BulkMeasure)
open QuantumNLS.QuantileForm (uI exists_pullback)
open QuantumNLS.QuantileTransport (qm empirical W2)
open PhysicalTensor (L2T)

set_option maxHeartbeats 8000000 in
theorem deterministic_gap_spec {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L)
    (hu : ‖u‖ = 1) (hbulk : BulkMeasure (Mu hκ u))
    {b a : ℤ} (hab : b < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0))
    (hend : EmpiricalWeakConv (fun n : ℕ => arrRoots L (κ / ((n : ℝ) + 1)) (η n)) (Mu hκ u))
    (hW2 : Tendsto (fun n : ℕ => W2 (empirical (n + 1) (arrRoots L (κ / ((n : ℝ) + 1)) (η n)))
      (Mu hκ u)) atTop (𝓝 0))
    {F : L2Unit} (hF : (⟨L, κ, Fact.out, hκ, Mu hκ u, hbulk⟩ : BulkResponseData).IsResponse F)
    {f : ℝ → ℝ} (hfm : Measurable f) (hFf : (F : ℝ → ℝ) =ᵐ[uI] fun t => f (qm (Mu hκ u) t))
    (xl : ℝ → ℝ)
    (hxl : ∀ k : ℤ, b ≤ k → k < a → ∀ lam : ℝ, (k : ℝ) < lam → lam < (k : ℝ) + 1 →
      th hκ u (xl lam) = lam * Real.pi) :
    IntervalIntegrable (fun lam => fext L κ (Mu hκ u) f (xl lam)) volume (b : ℝ) a ∧
    Tendsto (fun n : ℕ => ∑ i, arrRoots L (κ / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a) i ^ 2 -
        ∑ i, arrRoots L (κ / ((n : ℝ) + 1)) (η n) i ^ 2) atTop
      (𝓝 (4 * Real.pi * ∫ lam in (b : ℝ)..(a : ℝ), fext L κ (Mu hκ u) f (xl lam))) := by
  exact QuantumNLS.DetGapFinal.deterministic_gap hκ u hu hbulk hab hb ha η hηb hη hend hW2 hF hfm hFf xl hxl

end QuantumNLS.RC455Spec
#print axioms QuantumNLS.RC455Spec.deterministic_gap_spec
