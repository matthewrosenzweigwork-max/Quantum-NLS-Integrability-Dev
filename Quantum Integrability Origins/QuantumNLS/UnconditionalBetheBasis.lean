import QuantumNLS.AbstractContinuityProof
import QuantumNLS.ConditionalBetheNormality

/-!
# Unconditional Bethe basis: BCB1 / CBN1 instantiated with the proved `AbstractContinuity`

Authorized step: NEW VERIFIED OWNER AUTHORIZATION — EXT-001 full step
(`implementation/ops/STATUS.md`, 2026-11-15 13:58:00 UTC).

`AbstractContinuityProof.abstractContinuity : BetheConditionalBasis.AbstractContinuity` (ACP1) is
supplied as the single premise `hcont` of the frozen conditional results of BCB1
(`BetheConditionalBasis`, `b1d403e1…`) and CBN1 (`ConditionalBetheNormality`, `1b01115f…`, which
instantiates NB1 `NormalityBridge`, `4b68599d…`). All three are imported read-only and unchanged;
every statement below is the corresponding frozen statement with `hcont := abstractContinuity`.

* `density`, `dense`: Bethe waves span densely (R-8E4D05E7 density, every `N ≥ 1`, `c ≥ 0`);
* `basis`, `meanField_basis`: the full printed `basis:thm:basis` conclusion `BasisConclusion`;
* `physicalBasis`, `physicalBasis_position`, `coefficientTransform`, `coefficientTransform_apply`,
  `meanField_physicalBasis`, `bornLaw_hasSum_one`: the physical `MArr N` Hilbert basis, DEF-007;
* `meanField_isBetheBasis`, `transfer_physicalBasis`, `normal_deriv_physical`,
  `commute_deriv_physical`, `transfer_moments_physical`, `transfer_moments_deriv_physical`:
  the CBN1 / NB1 PROP-008 consequences for the actual physical basis.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped InnerProductSpace ComplexConjugate NNReal

namespace QuantumNLS.UnconditionalBetheBasis

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
  QuantumNLS.HighMomentsRank QuantumNLS.NormalizedTransfer QuantumNLS.HighMomentsTransfer
  QuantumNLS.HighMomentsDerivative QuantumNLS.BetheCoefficientTransform QuantumNLS.HighMomentsOps
  QuantumNLS.HighMomentsFinal QuantumNLS.NormalityBridge QuantumNLS.BetheConditionalBasis
  QuantumNLS.BethePhysicalTransfer QuantumNLS.ContactOperator QuantumNLS.BetheFreeFamily
  QuantumNLS.BetheContinuityInputs QuantumNLS.BetheBasisOrthogonality
  QuantumNLS.AbstractContinuityProof

/-- Bethe waves span densely, `N + 1 ≥ 1` particles, every `c ≥ 0` (unconditional). -/
theorem density (L : ℝ) [Fact (0 < L)] (N : ℕ) (c : ℝ≥0) :
    (Submodule.span ℂ (range (wave (L := L) c : Label (N+1) → SymL2 L (N+1)))).topologicalClosure = ⊤ :=
  density_from_continuity abstractContinuity L N c

/-- Same, through BCB1's `dense` (one-particle branch by the frozen Fourier proof). -/
theorem dense (L : ℝ) [Fact (0 < L)] (N : ℕ) (c : ℝ≥0) :
    (Submodule.span ℂ (range (wave (L := L) c : Label (N+1) → SymL2 L (N+1)))).topologicalClosure = ⊤ :=
  BetheConditionalBasis.dense abstractContinuity L N c

/-- **R-8E4D05E7, unconditional**: the full printed basis conclusion, every `N ≥ 1`, `c > 0`. -/
theorem basis (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :
    BasisConclusion L N ⟨c, hc.le⟩ :=
  BetheConditionalBasis.basis abstractContinuity L N hN c hc

/-- Mean-field specialization `c = κ/N`, unconditional. -/
theorem meanField_basis (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) {κ : ℝ} (hκ : 0 < κ) :
    BasisConclusion L N ⟨κ / N, (div_pos hκ (by exact_mod_cast hN)).le⟩ :=
  BetheConditionalBasis.meanField_basis abstractContinuity L N hN hκ

/-- The physical Bethe Hilbert basis of `Sym^N L²(T_L)`, indexed by `MArr N` (unconditional). -/
def physicalBasis (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :
    HilbertBasis (BetheLabels.MArr N) ℂ (physSector L N) :=
  BetheConditionalBasis.physicalBasis abstractContinuity L N hN c hc

theorem physicalBasis_position (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c)
    (m : BetheLabels.MArr N) :
    symmetricPosition L N (physicalBasis L N hN c hc m) =
      normalizedWave L N ⟨c, hc.le⟩ ((labelArr N).symm m) :=
  BetheConditionalBasis.physicalBasis_position abstractContinuity L N hN c hc m

/-- DEF-007 coefficient transform of the actual Bethe basis (unconditional). -/
def coefficientTransform (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :
    (physSector L N) ≃ₗᵢ[ℂ] lp (fun _ : BetheLabels.MArr N => ℂ) 2 :=
  BetheConditionalBasis.coefficientTransform abstractContinuity L N hN c hc

theorem coefficientTransform_apply (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ)
    (hc : 0 < c) (ψ : physSector L N) (m : BetheLabels.MArr N) :
    coefficientTransform L N hN c hc ψ m =
      ⟪normalizedWave L N ⟨c, hc.le⟩ ((labelArr N).symm m), symmetricPosition L N ψ⟫_ℂ :=
  BetheConditionalBasis.coefficientTransform_apply abstractContinuity L N hN c hc ψ m

/-- The physical basis at exactly `κ/N` (unconditional). -/
def meanField_physicalBasis (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) {κ : ℝ} (hκ : 0 < κ) :
    HilbertBasis (BetheLabels.MArr N) ℂ (physSector L N) :=
  BetheConditionalBasis.meanField_physicalBasis abstractContinuity L N hN hκ

/-- DEF-007 product-state law has total mass one (unconditional). -/
theorem bornLaw_hasSum_one (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c)
    (u : L2T L) (hu : ‖u‖ = 1) :
    HasSum (BetheCoefficientTransform.bornLaw (physicalBasis L N hN c hc) u) 1 :=
  BetheConditionalBasis.bornLaw_hasSum_one abstractContinuity L N hN c hc u hu

section Physical

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
include hκ hN

/-- The physical basis is a supplied complete Bethe basis (NB1 `IsBetheBasis`), unconditional. -/
theorem meanField_isBetheBasis : IsBetheBasis κ hκ hN (meanField_physicalBasis L N hN hκ) :=
  ConditionalBetheNormality.meanField_isBetheBasis abstractContinuity hκ hN

/-- `S_N(z)` is diagonal in the physical Bethe basis (unconditional). -/
theorem transfer_physicalBasis (z : ℂ) (m : QuantumNLS.BetheLabels.MArr N) :
    normalizedTransfer L κ N z (meanField_physicalBasis L N hN hκ m) =
      eigen (L := L) κ hκ hN m z • meanField_physicalBasis L N hN hκ m :=
  ConditionalBetheNormality.transfer_physicalBasis abstractContinuity hκ hN z m

/-- Every `∂_z^k S_N(z)` is normal (PROP-008 `hnormal`), unconditional. -/
theorem normal_deriv_physical (k : ℕ) (z : ℂ) :
    Commute (ContinuousLinearMap.adjoint (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z))
      (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z) :=
  ConditionalBetheNormality.normal_deriv_physical abstractContinuity hκ hN k z

/-- All spectral derivatives commute, unconditional. -/
theorem commute_deriv_physical (k l : ℕ) (z w : ℂ) :
    Commute (iteratedDeriv k (fun v => normalizedTransfer L κ N v) z)
      (iteratedDeriv l (fun v => normalizedTransfer L κ N v) w) :=
  ConditionalBetheNormality.commute_deriv_physical abstractContinuity hκ hN k l z w

/-- **PROP-008 actual-transfer moments**, unconditional. -/
theorem transfer_moments_physical {b' : ℝ} (hb' : 0 ≤ b') (u : L2T L) (hu : ‖u‖ = 1) (z : ℂ)
    (hz : -b' ≤ z.im) {p : ℕ} (hp : 1 ≤ p) :
    ⟪wvec N u, ((ContinuousLinearMap.adjoint (normalizedTransfer L κ N z - productSymbol L κ u z •
        (1 : BoundedSymmetricKernel (L2T L) N)) *
        (normalizedTransfer L κ N z - productSymbol L κ u z •
          (1 : BoundedSymmetricKernel (L2T L) N))) ^ p) (wvec N u)⟫_ℂ =
      ((‖((normalizedTransfer L κ N z - productSymbol L κ u z •
          (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 : ℝ) : ℂ) ∧
    ‖((normalizedTransfer L κ N z - productSymbol L κ u z •
        (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 ≤
      Cunif L κ b' p / (N : ℝ) ^ p :=
  ConditionalBetheNormality.transfer_moments_physical abstractContinuity hκ hN hb' u hu z hz hp

/-- **PROP-008 spectral-parameter derivative clause**, unconditional. -/
theorem transfer_moments_deriv_physical {b' R : ℝ} (hb' : 0 ≤ b') (hR : 0 < R) (u : L2T L)
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
      Cder L κ b' R k p / (N : ℝ) ^ p :=
  ConditionalBetheNormality.transfer_moments_deriv_physical abstractContinuity hκ hN hb' hR u hu z
    hz k hp

end Physical

end QuantumNLS.UnconditionalBetheBasis

#print axioms QuantumNLS.UnconditionalBetheBasis.density
#print axioms QuantumNLS.UnconditionalBetheBasis.dense
#print axioms QuantumNLS.UnconditionalBetheBasis.basis
#print axioms QuantumNLS.UnconditionalBetheBasis.meanField_basis
#print axioms QuantumNLS.UnconditionalBetheBasis.physicalBasis
#print axioms QuantumNLS.UnconditionalBetheBasis.physicalBasis_position
#print axioms QuantumNLS.UnconditionalBetheBasis.coefficientTransform
#print axioms QuantumNLS.UnconditionalBetheBasis.coefficientTransform_apply
#print axioms QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis
#print axioms QuantumNLS.UnconditionalBetheBasis.bornLaw_hasSum_one
#print axioms QuantumNLS.UnconditionalBetheBasis.meanField_isBetheBasis
#print axioms QuantumNLS.UnconditionalBetheBasis.transfer_physicalBasis
#print axioms QuantumNLS.UnconditionalBetheBasis.normal_deriv_physical
#print axioms QuantumNLS.UnconditionalBetheBasis.commute_deriv_physical
#print axioms QuantumNLS.UnconditionalBetheBasis.transfer_moments_physical
#print axioms QuantumNLS.UnconditionalBetheBasis.transfer_moments_deriv_physical
