import QuantumNLS.VarSelection
/-! integrator-authored trusted spec for R-C88B5D59 CC:F04:variable-coupling, selection and separation clauses (review record r21 FULL ACCEPT): headline statement(s) copied verbatim from VarSelection (QuantumNLS.VarSelection). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace QuantumNLS.RC88BSpecB
open QuantumNLS.VarSelection
open QuantumNLS.BetheLabels QuantumNLS.AdjacentResponse QuantumNLS.F02FiniteGap
open QuantumNLS.LocalHeight QuantumNLS.F04SelRank QuantumNLS.F04SelSetup QuantumNLS.F04SelBand
open QuantumNLS.VarCoupling
open PhysicalTensor (L2T)

set_option maxHeartbeats 8000000 in
theorem selectionV_spec {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) {κs : ℕ → ℝ}
    (hκs : Tendsto κs atTop (𝓝 κ)) (hpos : ∀ N, 0 < κs N) (u : L2T L) (hu : ‖u‖ = 1)
    {b a k : ℤ} (hbk : b ≤ k) (hka : k < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0))
    (hend : EmpiricalWeakConv (fun n : ℕ => arrRoots L (κs n / ((n : ℝ) + 1)) (η n)) (Mu hκ u))
    {lam : ℝ} (h1 : (k : ℝ) < lam) (h2 : lam < (k : ℝ) + 1) :
    (∃ x, th hκ u x = lam * Real.pi) ∧
    (∀ x, th hκ u x = lam * Real.pi →
      Tendsto (fun n : ℕ => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a
        (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)) atTop (𝓝 x)) ∧
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ n : ℕ in atTop, ∀ j : Fin (n + 1), j ≠ rk (η n) (hηb n) hbk →
      c₀ ≤ |qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a
          (sParam (η n) (hηb n) (a := a) hbk lam) j -
        qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a
          (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)| := by
  exact QuantumNLS.VarSelection.selectionV hκ hκs hpos u hu hbk hka hb ha η hηb hη hend h1 h2

end QuantumNLS.RC88BSpecB
#print axioms QuantumNLS.RC88BSpecB.selectionV_spec
