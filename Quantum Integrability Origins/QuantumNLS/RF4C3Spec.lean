import QuantumNLS.F04Selection
/-! integrator-authored trusted spec for R-F4C3E5BE CC:F04:selection (review record r20 FULL ACCEPT): headline statement(s) copied verbatim from F04Selection (QuantumNLS.F04Selection). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace QuantumNLS.RF4C3Spec
open QuantumNLS.F04Selection
open QuantumNLS.BetheLabels QuantumNLS.AdjacentResponse QuantumNLS.F02FiniteGap
open QuantumNLS.LocalHeight QuantumNLS.F04SelRank QuantumNLS.F04SelSetup QuantumNLS.F04SelBand
  QuantumNLS.F04SelConv
open PhysicalTensor (L2T)

set_option maxHeartbeats 8000000 in
theorem selection_spec {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    {b a k : ℤ} (hbk : b ≤ k) (hka : k < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0))
    (hend : EmpiricalWeakConv (fun n : ℕ => arrRoots L (κ / ((n : ℝ) + 1)) (η n)) (Mu hκ u))
    {lam : ℝ} (h1 : (k : ℝ) < lam) (h2 : lam < (k : ℝ) + 1) :
    (∃ x, th hκ u x = lam * Real.pi) ∧
    (∀ x, th hκ u x = lam * Real.pi →
      Tendsto (fun n : ℕ => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
        (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)) atTop (𝓝 x)) ∧
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ n : ℕ in atTop, ∀ j : Fin (n + 1), j ≠ rk (η n) (hηb n) hbk →
      c₀ ≤ |qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
          (sParam (η n) (hηb n) (a := a) hbk lam) j -
        qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
          (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)| := by
  exact QuantumNLS.F04Selection.selection hκ u hu hbk hka hb ha η hηb hη hend h1 h2

end QuantumNLS.RF4C3Spec
#print axioms QuantumNLS.RF4C3Spec.selection_spec
