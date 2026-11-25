import QuantumNLS.TerraMultiRound19ProductTerms

/-! Scaled fixed-overlap kernel limits used in commutator expansions. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Finset
open QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion QuantumNLS.PlacementProduct
open QuantumNLS.OverlapMoments
namespace QuantumNLS.TerraMultiRound19ScaledTerms

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem scaled_multiple_overlap_limit (p q s : ℕ) (hs : 2 ≤ s) (hsq : s ≤ q) :
    Tendsto (fun N : ℕ => (N : ℝ) * overlapCoefficient N p q s) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun N => mul_nonneg (Nat.cast_nonneg N)
    (overlapCoefficient_nonneg N p q s)) ?_ (tendsto_N_tail p q)
  apply Eventually.of_forall
  intro N
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  apply Finset.single_le_sum (fun j _ => overlapCoefficient_nonneg N p q j)
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The single-overlap kernel survives the commutator scaling with weight pq. -/
theorem scaled_single_overlap_term_limit (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N p q 1 : ℝ) : ℂ) •
      averagedOverlapKernel hp hq A B) atTop
      (𝓝 ((((p : ℝ) * q : ℝ) : ℂ) • averagedOverlapKernel hp hq A B)) := by
  have hc : Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N p q 1 : ℝ) : ℂ))
      atTop (𝓝 (((p : ℝ) * q : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_N_c_one p q)
  exact hc.smul tendsto_const_nhds

/-- Every fixed overlap of order at least two disappears after scaling by N. -/
theorem scaled_multiple_overlap_term_limit (p q s : ℕ) (hs : 2 ≤ s)
    (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N p q s : ℝ) : ℂ) •
      averagedOverlapKernel hsp hsq A B) atTop (𝓝 0) := by
  have hc : Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N p q s : ℝ) : ℂ))
      atTop (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (scaled_multiple_overlap_limit p q s hs hsq)
  let K := averagedOverlapKernel hsp hsq A B
  have ht : Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N p q s : ℝ) : ℂ) • K)
      atTop (𝓝 ((0 : ℂ) • K)) := hc.smul tendsto_const_nhds
  have hz : (0 : ℂ) • K = (0 : BoundedSymmetricKernel H (unionSize p q s)) := by
    ext x
    simp
  rw [hz] at ht
  exact ht

#print axioms scaled_multiple_overlap_limit
#print axioms scaled_single_overlap_term_limit
#print axioms scaled_multiple_overlap_term_limit
end QuantumNLS.TerraMultiRound19ScaledTerms
