import QuantumNLS.NormalityBridge

/-!
# The BCB1 conditional physical Bethe basis is a supplied complete Bethe basis

BCB1 (`BetheConditionalBasis`, `b1d403e1…`, read-only) constructs, under its single explicit premise
`hcont : AbstractContinuity` (R-9BF8373D, EXT-001), the physical Bethe Hilbert basis at mean-field
coupling `κ/N`, `meanField_physicalBasis`, whose `m`-th vector is the normalized source wave
`‖ψ_{n,κ/N}‖⁻¹ ψ_{n,κ/N}` with `n = (labelArr)⁻¹ m` (`physicalBasis_position`).

Here: `meanField_isBetheBasis` — this basis satisfies NB1's `IsBetheBasis` (the source wave is the
BSC1 `sourceVector`, `BetheBasisOrthogonality.source_position`). Consequently the PROP-008 normality
premises and moment statements hold for the actual physical basis, conditional only on `hcont`,
which is taken as an explicit hypothesis exactly as BCB1 does (not proved, approached or used
otherwise). Imports NB1 `NormalityBridge` (`4b68599d…`) read-only.
-/

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace ComplexConjugate NNReal

namespace QuantumNLS.ConditionalBetheNormality

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
  QuantumNLS.HighMomentsRank QuantumNLS.NormalizedTransfer QuantumNLS.HighMomentsTransfer
  QuantumNLS.HighMomentsDerivative QuantumNLS.BetheCoefficientTransform QuantumNLS.HighMomentsOps
  QuantumNLS.HighMomentsFinal QuantumNLS.NormalityBridge QuantumNLS.BetheConditionalBasis
  QuantumNLS.BethePhysicalTransfer

variable {L : ℝ} [Fact (0 < L)]

/-- **BCB1's conditional physical basis is a supplied complete Bethe basis** (`IsBetheBasis`),
for every `κ > 0`, `N ≥ 1`, under the explicit BCB1 premise `hcont`. -/
theorem meanField_isBetheBasis (hcont : AbstractContinuity) {κ : ℝ} (hκ : 0 < κ) {N : ℕ}
    (hN : 0 < N) : IsBetheBasis κ hκ hN (meanField_physicalBasis hcont L N hN hκ) := by
  intro m
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hc : 0 < κ / ((n + 1 : ℕ) : ℝ) := cpos hκ hN
  refine ⟨(‖sourceWave L (n + 1) ⟨κ / ((n + 1 : ℕ) : ℝ), hc.le⟩ (label m)‖⁻¹ : ℂ), ?_⟩
  apply (symmetricPosition L (n + 1)).injective
  have hpos := physicalBasis_position hcont L (n + 1) hN (κ / ((n + 1 : ℕ) : ℝ)) hc m
  rw [map_smul, BetheBasisOrthogonality.source_position]
  refine hpos.trans ?_
  unfold normalizedWave
  congr 1
  show BetheContinuityInputs.wave (L := L) ⟨κ / ((n + 1 : ℕ) : ℝ), hc.le⟩ (label m) = _
  rw [BetheContinuityInputs.wave_pos (L := L) (c := ⟨κ / ((n + 1 : ℕ) : ℝ), hc.le⟩) hc]
  rfl

section Physical

variable (hcont : AbstractContinuity) {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
include hcont hκ hN

/-- Conditional on `hcont`: `S_N(z)` is diagonal in the physical Bethe basis with the Bethe
transfer eigenvalue. -/
theorem transfer_physicalBasis (z : ℂ) (m : QuantumNLS.BetheLabels.MArr N) :
    normalizedTransfer L κ N z (meanField_physicalBasis hcont L N hN hκ m) =
      eigen (L := L) κ hκ hN m z • meanField_physicalBasis hcont L N hN hκ m :=
  transfer_basis hκ hN (meanField_isBetheBasis hcont hκ hN) z m

/-- Conditional on `hcont`: every `∂_z^k S_N(z)` is normal (the PROP-008 `hnormal`). -/
theorem normal_deriv_physical (k : ℕ) (z : ℂ) :
    Commute (ContinuousLinearMap.adjoint (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z))
      (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z) :=
  normal_deriv hκ hN (meanField_isBetheBasis hcont hκ hN) k z

/-- Conditional on `hcont`: all spectral derivatives commute. -/
theorem commute_deriv_physical (k l : ℕ) (z w : ℂ) :
    Commute (iteratedDeriv k (fun v => normalizedTransfer L κ N v) z)
      (iteratedDeriv l (fun v => normalizedTransfer L κ N v) w) :=
  commute_deriv hκ hN (meanField_isBetheBasis hcont hκ hN) k l z w

/-- **PROP-008 actual-transfer moments for the physical Bethe basis, conditional on `hcont`.** -/
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
  transfer_moments_bethe hκ hN (meanField_isBetheBasis hcont hκ hN) hb' u hu z hz hp

/-- **PROP-008 spectral-parameter derivative clause for the physical Bethe basis, conditional on
`hcont`.** -/
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
  transfer_moments_deriv_bethe hκ hN (meanField_isBetheBasis hcont hκ hN) hb' hR u hu z hz k hp

end Physical

#print axioms meanField_isBetheBasis
#print axioms transfer_physicalBasis
#print axioms normal_deriv_physical
#print axioms commute_deriv_physical
#print axioms transfer_moments_physical
#print axioms transfer_moments_deriv_physical

end QuantumNLS.ConditionalBetheNormality
