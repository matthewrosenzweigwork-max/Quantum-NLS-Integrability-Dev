import QuantumNLS.RootMassInvolutionBatchR9
/-! integrator-authored trusted spec for R-507DD869 thm:root-mass-involution (review record r19 FULL ACCEPT): headline statement(s) copied verbatim from RootMassInvolutionBatchR9 (QuantumNLS.RootMassInvolutionR9). -/
set_option autoImplicit false
set_option maxErrors 200
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Topology
namespace QuantumNLS.R507Spec
open QuantumNLS.RootMassInvolutionR9
open PhysicalTensor (L2T)
open RootMassInvolutionR8 (mass)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9
open RootBracketContinuationR9 RootMassDifferentialR9 SymplecticBracket
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_mass_involution_spec (hκ : 0 < κ) :
    (∀ (n : ℤ) (u : L2T L), AnalyticAt ℝ (mass hκ n) u) ∧
    (∀ (n m : ℤ) (u : L2T L), pbR (mass hκ n) (mass hκ m) u = 0) := by
  exact QuantumNLS.RootMassInvolutionR9.root_mass_involution hκ

end QuantumNLS.R507Spec
#print axioms QuantumNLS.R507Spec.root_mass_involution_spec
