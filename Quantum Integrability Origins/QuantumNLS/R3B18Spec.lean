import QuantumNLS.HaarKernelTailMain
/-! integrator-authored trusted spec for R-3B18A493 QG:prop:haar-kernel-tail (Terra r138 ACCEPT): frozen statements restated verbatim. -/
namespace R3B18Spec
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter Topology Finset Metric
open QuantumNLS.HaarEigenbasis QuantumNLS.HaarSlaterBasis QuantumNLS.HaarKernelFactorizationSym
open QuantumNLS.GridEigen QuantumNLS.GridBounds QuantumNLS.HilbertDiagOp QuantumNLS.GridStrongSum
open QuantumNLS.HaarKernelTailBounds QuantumNLS.HaarKernelTailPointwise
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.BethePhysicalTransfer
open QuantumNLS QuantumNLS.HaarKernelTailMain

set_option maxHeartbeats 4000000 in
theorem haar_kernel_tail_compact_spec (L : ℝ) [Fact (0 < L)] (n : ℕ) (T : (ℤ → ℂ) → (Hn L n →L[ℂ] Hn L n))
    (hT : ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) → ∀ v,
      Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T t v)))
    (C : Set (Hn L n)) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) →
      (∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0) → ∀ f ∈ C, ‖T t f‖ ≤ ε := by
  apply QuantumNLS.HaarKernelTailMain.haar_kernel_tail_compact <;> assumption

set_option maxHeartbeats 4000000 in
theorem R_3B18A493_spec (L : ℝ) [Fact (0 < L)] (n : ℕ) (T : (ℤ → ℂ) → (Hn L n →L[ℂ] Hn L n))
    (hT : ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) → ∀ v,
      Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T t v))) :
    (Even n → ∀ (R : ℕ) (k : Idx (n + 1)), (∀ j : Fin (n + 1), |k.1 j| ≤ (R : ℤ)) →
        ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) → (∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0) →
        T t (physBasis L n k) = 0) ∧
    (Odd n → ∀ (k : Idx (n + 1)) (M : ℝ), (∀ j : Fin (n + 1), |(k.1 j : ℝ) + 1 / 2| ≤ M) →
        ∀ (R : ℕ), 2 * M + 1 < (R : ℝ) → ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) →
        (∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0) →
        ‖muGrid L n t k‖ ≤ 2 ^ (n + 1 + 2) / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1) *
          (n : ℝ)) * ((R : ℝ) - 1) ^ (1 - ((n + 1 : ℕ) : ℤ))) ∧
    (∀ (C : Set (Hn L n)), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
        ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) → (∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0) →
        ∀ f ∈ C, ‖T t f‖ ≤ ε) := by
  apply QuantumNLS.HaarKernelTailMain.R_3B18A493 <;> assumption

end R3B18Spec
#print axioms R3B18Spec.haar_kernel_tail_compact_spec
#print axioms R3B18Spec.R_3B18A493_spec
