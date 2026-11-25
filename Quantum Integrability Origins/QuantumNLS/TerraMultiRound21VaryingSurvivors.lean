import QuantumNLS.TerraMultiRound21VaryingAverage
import QuantumNLS.TerraMultiRound19ScaledTerms

/-! Surviving fixed-overlap terms for varying input kernels. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion QuantumNLS.PlacementProduct
open QuantumNLS.TerraMultiRound18OverlapLimit QuantumNLS.TerraMultiRound21VaryingAverage
namespace QuantumNLS.TerraMultiRound21VaryingSurvivors
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem varying_zero_overlap_term_limit (p q : ℕ)
    (A : ℕ → BoundedSymmetricKernel H p) (B : ℕ → BoundedSymmetricKernel H q)
    (A₀ : BoundedSymmetricKernel H p) (B₀ : BoundedSymmetricKernel H q)
    (hA : Tendsto (fun N => ‖A N - A₀‖) atTop (𝓝 0))
    (hB : Tendsto (fun N => ‖B N - B₀‖) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((overlapCoefficient N p q 0 : ℝ) : ℂ) •
      averagedOverlapKernel (Nat.zero_le p) (Nat.zero_le q) (A N) (B N)) atTop
      (𝓝 (averagedOverlapKernel (Nat.zero_le p) (Nat.zero_le q) A₀ B₀)) := by
  have hc : Tendsto (fun N : ℕ => ((overlapCoefficient N p q 0 : ℝ) : ℂ)) atTop (𝓝 1) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (zero_overlap_tendsto_one p q)
  have hk := varying_average_limit (Nat.zero_le p) (Nat.zero_le q) A B A₀ B₀ hA hB
  have ht := hc.smul hk
  simpa only [one_smul] using ht

theorem varying_scaled_single_overlap_term_limit (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (A : ℕ → BoundedSymmetricKernel H p) (B : ℕ → BoundedSymmetricKernel H q)
    (A₀ : BoundedSymmetricKernel H p) (B₀ : BoundedSymmetricKernel H q)
    (hA : Tendsto (fun N => ‖A N - A₀‖) atTop (𝓝 0))
    (hB : Tendsto (fun N => ‖B N - B₀‖) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N p q 1 : ℝ) : ℂ) •
      averagedOverlapKernel hp hq (A N) (B N)) atTop
      (𝓝 ((((p : ℝ) * q : ℝ) : ℂ) • averagedOverlapKernel hp hq A₀ B₀)) := by
  have hc : Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N p q 1 : ℝ) : ℂ))
      atTop (𝓝 (((p : ℝ) * q : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (QuantumNLS.OverlapMoments.tendsto_N_c_one p q)
  exact hc.smul (varying_average_limit hp hq A B A₀ B₀ hA hB)

#print axioms varying_zero_overlap_term_limit
#print axioms varying_scaled_single_overlap_term_limit
end QuantumNLS.TerraMultiRound21VaryingSurvivors
