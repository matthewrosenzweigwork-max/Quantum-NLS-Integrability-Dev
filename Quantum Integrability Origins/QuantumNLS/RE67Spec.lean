import QuantumNLS.GridStrongSumGeneral
/-! integrator-authored trusted spec for R-E67FE3C4 QG:prop:haar-grid-weights (Terra r138 ACCEPT; AM-GM route for the grid bound recorded): frozen statements restated verbatim. -/
namespace RE67Spec
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter Topology Finset
open QuantumNLS.HaarEigenbasis QuantumNLS.HaarSlaterBasis QuantumNLS.HaarKernelFactorizationSym
open QuantumNLS.GridEigen QuantumNLS.GridBounds QuantumNLS.HilbertDiagOp QuantumNLS.GridStrongSum
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.BethePhysicalTransfer
open QuantumNLS QuantumNLS.GridStrongSumGeneral

set_option maxHeartbeats 4000000 in
theorem bounded_strong_limit_spec (L : ℝ) [Fact (0 < L)] (n : ℕ) (t : ℤ → ℂ) (hb : BddAbove (Set.range fun m => ‖t m‖)) :
    ∃ T : Hn L n →L[ℂ] Hn L n,
      (∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T v))) ∧
      ‖T‖ ≤ Bd L (n + 1) * ⨆ m, ‖t m‖ ∧
      (∀ T' : Hn L n →L[ℂ] Hn L n,
        (∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T' v))) → T' = T) ∧
      (∀ F : ℕ → Finset ℤ, (∀ N, F N ⊆ F (N + 1)) → (∀ m : ℤ, ∃ N, m ∈ F N) →
        ∀ v, Tendsto (fun N => ∑ m ∈ F N, t m • physicalKernel L (n + 1) (gridPt L m) v)
          atTop (𝓝 (T v))) := by
  apply QuantumNLS.GridStrongSumGeneral.bounded_strong_limit <;> assumption

set_option maxHeartbeats 4000000 in
theorem R_E67FE3C4_general_spec (L : ℝ) [Fact (0 < L)] :
    (∀ (n : ℕ) (t : ℤ → ℂ), BddAbove (Set.range fun m => ‖t m‖) →
      ∃ T : Hn L n →L[ℂ] Hn L n,
        (∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T v))) ∧
        ‖T‖ ≤ Bd L (n + 1) * ⨆ m, ‖t m‖ ∧
        (∀ T' : Hn L n →L[ℂ] Hn L n,
          (∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T' v))) → T' = T) ∧
        (∀ F : ℕ → Finset ℤ, (∀ N, F N ⊆ F (N + 1)) → (∀ m : ℤ, ∃ N, m ∈ F N) →
          ∀ v, Tendsto (fun N => ∑ m ∈ F N, t m • physicalKernel L (n + 1) (gridPt L m) v)
            atTop (𝓝 (T v)))) ∧
    (∀ (m : ℕ) (a κ : ℝ), 0 < κ → 0 ≤ a → ∃ S0 : ℝ, ∀ (t : ℤ → ℂ), (∀ j, ‖t j‖ ≤ 1) →
      ∀ T : (n : ℕ) → Hn L n →L[ℂ] Hn L n,
        (∀ n v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T n v))) →
        Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * ‖T n‖) ∧
        ∑' n : ℕ, ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * ‖T n‖ ≤ S0) := by
  apply QuantumNLS.GridStrongSumGeneral.R_E67FE3C4_general <;> assumption

end RE67Spec
#print axioms RE67Spec.bounded_strong_limit_spec
#print axioms RE67Spec.R_E67FE3C4_general_spec
