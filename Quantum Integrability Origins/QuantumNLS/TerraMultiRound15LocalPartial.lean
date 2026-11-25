import QuantumNLS.KernelConvergence
import QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011

/-! Partial support for LOCAL-013. This derives radius reduction for the
literal DEF-042 convergence predicate and records the accepted finite-sector
product expansion. It does not establish coefficient limits of products,
scalar functional calculus, or the commutator/Poisson limit. -/

set_option autoImplicit false
noncomputable section
open Filter Topology
open QuantumNLS.KernelDefinition QuantumNLS.LocalPlacement
open QuantumNLS.KernelConvergence

namespace QuantumNLS.TerraMultiRound15LocalPartial

/-- A convergent chosen family remains convergent on a nonnegative smaller
radius, with the same limiting kernels. -/
theorem convergence_radius_reduction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {r R : ℝ} (hr : 0 ≤ r) (h : r ≤ R)
    {A : ∀ N : ℕ, KernelList (H := H) N}
    {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hA : ConvergesOnRadius R A Alim) : ConvergesOnRadius r A Alim := by
  rcases hA with ⟨⟨C, hC⟩, hlim⟩
  refine ⟨⟨C, fun N => (le_trans ?_ (hC N))⟩, hlim⟩
  unfold QuantumNLS.RadiusBound.radiusBound
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr h p.1) (norm_nonneg (A N p))

#print axioms convergence_radius_reduction

end QuantumNLS.TerraMultiRound15LocalPartial
