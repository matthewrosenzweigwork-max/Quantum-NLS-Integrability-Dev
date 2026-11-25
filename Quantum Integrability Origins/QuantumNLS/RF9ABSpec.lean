import QuantumNLS.OffgridCommutator
/-! integrator-authored trusted spec for R-F9AB39A7 QG:lem:haar-offgrid-bessel (Terra r134 ACCEPT for positive marginal rank): frozen statements of OffgridCommutator restated verbatim. -/
namespace RF9ABSpec
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.PlacementGrouping QuantumNLS.RootOverlapCommutator QuantumNLS.PlacementCommutatorL2
open QuantumNLS.OffgridBessel QuantumNLS.HaarEigenbasis QuantumNLS.HaarKernelFactorizationSym
  QuantumNLS.BethePhysicalTransfer QuantumNLS.PhysicalTensor QuantumNLS.NormalizedTransfer
  QuantumNLS.HighMomentsRank QuantumNLS.DiagonalBesselStrong QuantumNLS.HaarSlaterBasis
open QuantumNLS QuantumNLS.OffgridCommutator

set_option maxHeartbeats 4000000 in
theorem haar_kernel_bessel_spec (L : ℝ) [Fact (0 < L)] {w : ℂ} (hw : w ∈ Gamma0 L) (n : ℕ) :
    (∃ T : SymSector ℂ (L2T L) (n + 1) →L[ℂ] SymSector ℂ (L2T L) (n + 1),
      (∀ x, HasSum (fun j : ℤ => (ContinuousLinearMap.adjoint (physicalKernel L (n + 1) (zpt L w j)) ∘L
        physicalKernel L (n + 1) (zpt L w j)) x) (T x)) ∧
      (∀ x, ⟪x, T x⟫_ℂ = ((∑' j : ℤ, ‖physicalKernel L (n + 1) (zpt L w j) x‖ ^ 2 : ℝ) : ℂ)) ∧
      (∀ x, Summable (fun j : ℤ => ‖physicalKernel L (n + 1) (zpt L w j) x‖ ^ 2) ∧
        ∑' j : ℤ, ‖physicalKernel L (n + 1) (zpt L w j) x‖ ^ 2 ≤ bR L (n + 1) ^ 2 * ‖x‖ ^ 2) ∧
      T.IsPositive) ∧
    (∃ T : SymSector ℂ (L2T L) (n + 1) →L[ℂ] SymSector ℂ (L2T L) (n + 1),
      (∀ x, HasSum (fun j : ℤ => (physicalKernel L (n + 1) (zpt L w j) ∘L
        ContinuousLinearMap.adjoint (physicalKernel L (n + 1) (zpt L w j))) x) (T x)) ∧
      (∀ x, ⟪x, T x⟫_ℂ = ((∑' j : ℤ, ‖ContinuousLinearMap.adjoint (physicalKernel L (n + 1) (zpt L w j)) x‖ ^ 2 : ℝ) : ℂ)) ∧
      (∀ x, Summable (fun j : ℤ => ‖ContinuousLinearMap.adjoint (physicalKernel L (n + 1) (zpt L w j)) x‖ ^ 2) ∧
        ∑' j : ℤ, ‖ContinuousLinearMap.adjoint (physicalKernel L (n + 1) (zpt L w j)) x‖ ^ 2 ≤
          bR L (n + 1) ^ 2 * ‖x‖ ^ 2) ∧
      T.IsPositive) := by
  apply QuantumNLS.OffgridCommutator.haar_kernel_bessel <;> assumption

set_option maxHeartbeats 4000000 in
theorem summable_Bk_spec (L : ℝ) [Fact (0 < L)] (κ : ℝ) : Summable (fun j : ℕ => ((j : ℝ) + 1) * κ ^ (j + 1) * bR L (j + 1)) := by
  apply QuantumNLS.OffgridCommutator.summable_Bk <;> assumption

set_option maxHeartbeats 4000000 in
theorem haar_commutator_bessel_spec (L : ℝ) [Fact (0 < L)] {w : ℂ} (hw : w ∈ Gamma0 L) {κ : ℝ} (hκ : 0 ≤ κ) {N k : ℕ}
    (hk1 : 1 ≤ k) (hkN : k ≤ N) (J : BoundedSymmetricKernel (L2T L) k) (ψ : SymSector ℂ (L2T L) N) :
    Summable (fun j : ℤ => ((N : ℝ) * ‖(normalizedTransfer L κ N (zpt L w j) * genericU_N_r N k hkN J -
        genericU_N_r N k hkN J * normalizedTransfer L κ N (zpt L w j)) ψ‖) ^ 2) ∧
    Real.sqrt (∑' j : ℤ, ((N : ℝ) * ‖(normalizedTransfer L κ N (zpt L w j) * genericU_N_r N k hkN J -
        genericU_N_r N k hkN J * normalizedTransfer L κ N (zpt L w j)) ψ‖) ^ 2) ≤
      Bk L κ k * ‖J‖ * ‖ψ‖ := by
  apply QuantumNLS.OffgridCommutator.haar_commutator_bessel <;> assumption

set_option maxHeartbeats 4000000 in
theorem haar_commutator_bessel_adjoint_spec (L : ℝ) [Fact (0 < L)] {w : ℂ} (hw : w ∈ Gamma0 L) {κ : ℝ} (hκ : 0 ≤ κ) {N k : ℕ}
    (hk1 : 1 ≤ k) (hkN : k ≤ N) (J : BoundedSymmetricKernel (L2T L) k) (ψ : SymSector ℂ (L2T L) N) :
    Summable (fun j : ℤ => ((N : ℝ) * ‖(ContinuousLinearMap.adjoint (normalizedTransfer L κ N (zpt L w j)) *
        genericU_N_r N k hkN J - genericU_N_r N k hkN J *
          ContinuousLinearMap.adjoint (normalizedTransfer L κ N (zpt L w j))) ψ‖) ^ 2) ∧
    Real.sqrt (∑' j : ℤ, ((N : ℝ) * ‖(ContinuousLinearMap.adjoint (normalizedTransfer L κ N (zpt L w j)) *
        genericU_N_r N k hkN J - genericU_N_r N k hkN J *
          ContinuousLinearMap.adjoint (normalizedTransfer L κ N (zpt L w j))) ψ‖) ^ 2) ≤
      Bk L κ k * ‖J‖ * ‖ψ‖ := by
  apply QuantumNLS.OffgridCommutator.haar_commutator_bessel_adjoint <;> assumption

end RF9ABSpec
#print axioms RF9ABSpec.haar_kernel_bessel_spec
#print axioms RF9ABSpec.summable_Bk_spec
#print axioms RF9ABSpec.haar_commutator_bessel_spec
#print axioms RF9ABSpec.haar_commutator_bessel_adjoint_spec
