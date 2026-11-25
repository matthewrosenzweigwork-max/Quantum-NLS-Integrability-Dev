import QuantumNLS.UnconditionalBetheBasis
/-! integrator-authored trusted spec for PROP-008 lem:B4-high-moments for the PHYSICAL Bethe basis, κ > 0, N ≥ 1
(Terra r133 ACCEPT, combining HMT1/HMD1 moment bounds with NB1/CBN1 normality instantiated by the proved EXT-001):
transfer eigenrelation in the physical basis, normality and commutation of all spectral-parameter derivatives, and the
actual-transfer and derivative moment bounds; statements copied verbatim from UBB1. -/
namespace PROP008Spec
open Set Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate NNReal
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
  QuantumNLS.HighMomentsRank QuantumNLS.NormalizedTransfer QuantumNLS.HighMomentsTransfer
  QuantumNLS.HighMomentsDerivative QuantumNLS.BetheCoefficientTransform QuantumNLS.HighMomentsOps
  QuantumNLS.HighMomentsFinal QuantumNLS.NormalityBridge QuantumNLS.BetheConditionalBasis
  QuantumNLS.BethePhysicalTransfer QuantumNLS.ContactOperator QuantumNLS.BetheFreeFamily
  QuantumNLS.BetheContinuityInputs QuantumNLS.BetheBasisOrthogonality
  QuantumNLS.AbstractContinuityProof
open QuantumNLS QuantumNLS.UnconditionalBetheBasis

theorem transfer_physicalBasis_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (z : ℂ) (m : QuantumNLS.BetheLabels.MArr N) :
    normalizedTransfer L κ N z (meanField_physicalBasis L N hN hκ m) =
      eigen (L := L) κ hκ hN m z • meanField_physicalBasis L N hN hκ m := by
  apply QuantumNLS.UnconditionalBetheBasis.transfer_physicalBasis <;> assumption

theorem normal_deriv_physical_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (k : ℕ) (z : ℂ) :
    Commute (ContinuousLinearMap.adjoint (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z))
      (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z) := by
  apply QuantumNLS.UnconditionalBetheBasis.normal_deriv_physical <;> assumption

theorem commute_deriv_physical_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (k l : ℕ) (z w : ℂ) :
    Commute (iteratedDeriv k (fun v => normalizedTransfer L κ N v) z)
      (iteratedDeriv l (fun v => normalizedTransfer L κ N v) w) := by
  apply QuantumNLS.UnconditionalBetheBasis.commute_deriv_physical <;> assumption

theorem transfer_moments_physical_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {b' : ℝ} (hb' : 0 ≤ b') (u : L2T L) (hu : ‖u‖ = 1) (z : ℂ)
    (hz : -b' ≤ z.im) {p : ℕ} (hp : 1 ≤ p) :
    ⟪wvec N u, ((ContinuousLinearMap.adjoint (normalizedTransfer L κ N z - productSymbol L κ u z •
        (1 : BoundedSymmetricKernel (L2T L) N)) *
        (normalizedTransfer L κ N z - productSymbol L κ u z •
          (1 : BoundedSymmetricKernel (L2T L) N))) ^ p) (wvec N u)⟫_ℂ =
      ((‖((normalizedTransfer L κ N z - productSymbol L κ u z •
          (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 : ℝ) : ℂ) ∧
    ‖((normalizedTransfer L κ N z - productSymbol L κ u z •
        (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 ≤
      Cunif L κ b' p / (N : ℝ) ^ p := by
  apply QuantumNLS.UnconditionalBetheBasis.transfer_moments_physical <;> assumption

theorem transfer_moments_deriv_physical_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {b' R : ℝ} (hb' : 0 ≤ b') (hR : 0 < R) (u : L2T L)
    (hu : ‖u‖ = 1) (z : ℂ) (hz : -b' ≤ z.im) (k : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    ⟪wvec N u, ((ContinuousLinearMap.adjoint
        (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
          iteratedDeriv k (fun w => productSymbol L κ u w) z •
            (1 : BoundedSymmetricKernel (L2T L) N)) *
        (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
          iteratedDeriv k (fun w => productSymbol L κ u w) z •
            (1 : BoundedSymmetricKernel (L2T L) N))) ^ p) (wvec N u)⟫_ℂ =
      ((‖((iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
          iteratedDeriv k (fun w => productSymbol L κ u w) z •
            (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 : ℝ) : ℂ) ∧
    ‖((iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
        iteratedDeriv k (fun w => productSymbol L κ u w) z •
          (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 ≤
      Cder L κ b' R k p / (N : ℝ) ^ p := by
  apply QuantumNLS.UnconditionalBetheBasis.transfer_moments_deriv_physical <;> assumption

end PROP008Spec
#print axioms PROP008Spec.transfer_physicalBasis_spec
#print axioms PROP008Spec.normal_deriv_physical_spec
#print axioms PROP008Spec.commute_deriv_physical_spec
#print axioms PROP008Spec.transfer_moments_physical_spec
#print axioms PROP008Spec.transfer_moments_deriv_physical_spec
