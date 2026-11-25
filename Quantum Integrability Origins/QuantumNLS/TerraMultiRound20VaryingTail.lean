import QuantumNLS.TerraMultiRound19ScaledTerms
import QuantumNLS.TerraMultiRound20NormLimit

/-! Positive-overlap terms for norm-convergent varying input kernels. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion QuantumNLS.PlacementProduct
open QuantumNLS.TerraMultiRound19ProductTerms QuantumNLS.TerraMultiRound19ScaledTerms
open QuantumNLS.TerraMultiRound20NormLimit
namespace QuantumNLS.TerraMultiRound20VaryingTail

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem varying_positive_overlap_limit (p q s : ℕ) (hs : 1 ≤ s)
    (hsp : s ≤ p) (hsq : s ≤ q)
    (A : ℕ → BoundedSymmetricKernel H p) (B : ℕ → BoundedSymmetricKernel H q)
    (A₀ : BoundedSymmetricKernel H p) (B₀ : BoundedSymmetricKernel H q)
    (hA : Tendsto (fun N => ‖A N - A₀‖) atTop (𝓝 0))
    (hB : Tendsto (fun N => ‖B N - B₀‖) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((overlapCoefficient N p q s : ℝ) : ℂ) •
      averagedOverlapKernel hsp hsq (A N) (B N)) atTop (𝓝 0) := by
  apply vanishing_smul_of_norm_bound (E := BoundedSymmetricKernel H (unionSize p q s)) _ _ _ _ ‖A₀‖ ‖B₀‖
  · exact positive_overlap_coefficient_limit p q s hs hsq
  · exact fun N => overlapCoefficient_nonneg N p q s
  · exact QuantumNLS.KernelConvergence.norm_tendsto_of (E := BoundedSymmetricKernel H p) hA
  · exact QuantumNLS.KernelConvergence.norm_tendsto_of (E := BoundedSymmetricKernel H q) hB
  · exact fun N => norm_averagedOverlapKernel_le hsp hsq (A N) (B N)

theorem scaled_varying_multiple_overlap_limit (p q s : ℕ) (hs : 2 ≤ s)
    (hsp : s ≤ p) (hsq : s ≤ q)
    (A : ℕ → BoundedSymmetricKernel H p) (B : ℕ → BoundedSymmetricKernel H q)
    (A₀ : BoundedSymmetricKernel H p) (B₀ : BoundedSymmetricKernel H q)
    (hA : Tendsto (fun N => ‖A N - A₀‖) atTop (𝓝 0))
    (hB : Tendsto (fun N => ‖B N - B₀‖) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N p q s : ℝ) : ℂ) •
      averagedOverlapKernel hsp hsq (A N) (B N)) atTop (𝓝 0) := by
  apply vanishing_smul_of_norm_bound (E := BoundedSymmetricKernel H (unionSize p q s)) _ _ _ _ ‖A₀‖ ‖B₀‖
  · exact scaled_multiple_overlap_limit p q s hs hsq
  · exact fun N => mul_nonneg (Nat.cast_nonneg N) (overlapCoefficient_nonneg N p q s)
  · exact QuantumNLS.KernelConvergence.norm_tendsto_of (E := BoundedSymmetricKernel H p) hA
  · exact QuantumNLS.KernelConvergence.norm_tendsto_of (E := BoundedSymmetricKernel H q) hB
  · exact fun N => norm_averagedOverlapKernel_le hsp hsq (A N) (B N)

#print axioms varying_positive_overlap_limit
#print axioms scaled_varying_multiple_overlap_limit
end QuantumNLS.TerraMultiRound20VaryingTail
