import QuantumNLS.TerraMultiRound18OverlapLimit
import QuantumNLS.PlacementProduct

/-! Fixed input-degree overlap coefficients and product kernel terms. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Finset
open QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion QuantumNLS.PlacementProduct
open QuantumNLS.TerraMultiRound18OverlapLimit
namespace QuantumNLS.TerraMultiRound19ProductTerms

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positive_overlap_coefficient_limit (p q s : ℕ) (hs : 1 ≤ s) (hsq : s ≤ q) :
    Tendsto (fun N : ℕ => overlapCoefficient N p q s) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun N => overlapCoefficient_nonneg N p q s) ?_
    (positive_overlap_tendsto_zero p q)
  apply Eventually.of_forall
  intro N
  apply Finset.single_le_sum (fun j _ => overlapCoefficient_nonneg N p q j)
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- For fixed input kernels each positive-overlap product contribution tends
in operator norm to zero. -/
theorem positive_overlap_product_term_limit (p q s : ℕ) (hs : 1 ≤ s)
    (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    Tendsto (fun N : ℕ => ((overlapCoefficient N p q s : ℝ) : ℂ) •
      averagedOverlapKernel hsp hsq A B) atTop (𝓝 0) := by
  have hc : Tendsto (fun N : ℕ => ((overlapCoefficient N p q s : ℝ) : ℂ)) atTop (𝓝 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp (positive_overlap_coefficient_limit p q s hs hsq)
  let K := averagedOverlapKernel hsp hsq A B
  have ht : Tendsto (fun N : ℕ => ((overlapCoefficient N p q s : ℝ) : ℂ) • K)
      atTop (𝓝 ((0 : ℂ) • K)) := hc.smul tendsto_const_nhds
  have hz : (0 : ℂ) • K = (0 : BoundedSymmetricKernel H (unionSize p q s)) := by
    ext x
    simp
  rw [hz] at ht
  exact ht

/-- The no-overlap contribution tends in operator norm to the disjoint
averaged product kernel. -/
theorem zero_overlap_product_term_limit (p q : ℕ)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    Tendsto (fun N : ℕ => ((overlapCoefficient N p q 0 : ℝ) : ℂ) •
      averagedOverlapKernel (Nat.zero_le p) (Nat.zero_le q) A B) atTop
      (𝓝 (averagedOverlapKernel (Nat.zero_le p) (Nat.zero_le q) A B)) := by
  have hc : Tendsto (fun N : ℕ => ((overlapCoefficient N p q 0 : ℝ) : ℂ)) atTop (𝓝 1) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp (zero_overlap_tendsto_one p q)
  simpa using hc.smul (tendsto_const_nhds (x := averagedOverlapKernel (Nat.zero_le p) (Nat.zero_le q) A B))

#print axioms positive_overlap_coefficient_limit
#print axioms positive_overlap_product_term_limit
#print axioms zero_overlap_product_term_limit
end QuantumNLS.TerraMultiRound19ProductTerms
