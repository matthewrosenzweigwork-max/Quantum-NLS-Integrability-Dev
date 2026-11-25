import QuantumNLS.UnconditionalBetheBasis

/-!
LOCAL-009 round 50, stage 1: diagonalization of the actual normalized transfer.

The accepted unconditional Bethe basis and the transfer eigenrelation are reused
read-only. This module specializes that result to the physical basis at
coupling `κ / N` and records pairwise commutation of all spectral derivatives.
This is the transfer-side diagonalization constituent; operator functional
calculus for `g_z(S_ε(z))` and the contour operator are separate stages.
-/

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.LOCAL009Round50Diagonalization

open QuantumNLS.NormalityBridge QuantumNLS.NormalizedTransfer
  QuantumNLS.UnconditionalBetheBasis

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
  {N : ℕ} (hN : 0 < N)

/-- The accepted complete physical Bethe basis at mean-field coupling `κ/N`. -/
abbrev physicalBetheBasis :
    QuantumNLS.BetheCoefficientTransform.BetheBasis L N :=
  UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ

/-- The actual normalized transfer is diagonal in the accepted physical Bethe basis. -/
theorem transfer_diagonal (z : ℂ) :
    IsDiag (physicalBetheBasis hκ hN)
      (normalizedTransfer L κ N z) := by
  intro m
  exact ⟨eigen (L := L) κ hκ hN m z,
    UnconditionalBetheBasis.transfer_physicalBasis hκ hN z m⟩

/-- Every spectral derivative of the actual transfer is diagonal in that basis. -/
theorem derivative_diagonal (k : ℕ) (z : ℂ) :
    IsDiag (physicalBetheBasis hκ hN)
      (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z) := by
  intro m
  exact ⟨iteratedDeriv k (eigen (L := L) κ hκ hN m) z,
    QuantumNLS.NormalityBridge.deriv_basis hκ hN
      (UnconditionalBetheBasis.meanField_isBetheBasis hκ hN) k z m⟩

/-- All factors formed from spectral derivatives commute on the physical sector. -/
theorem transfer_derivatives_commute (hκ' : 0 < κ) (hN' : 0 < N)
    (k l : ℕ) (z w : ℂ) :
    Commute (iteratedDeriv k (fun v => normalizedTransfer L κ N v) z)
      (iteratedDeriv l (fun v => normalizedTransfer L κ N v) w) :=
  UnconditionalBetheBasis.commute_deriv_physical hκ' hN' k l z w

/-- In particular, the transfer and its first spectral derivative commute. -/
theorem transfer_commutes_with_derivative (hκ' : 0 < κ) (hN' : 0 < N) (z : ℂ) :
    Commute (normalizedTransfer L κ N z)
      (iteratedDeriv 1 (fun w => normalizedTransfer L κ N w) z) := by
  simpa only [iteratedDeriv_zero] using
    transfer_derivatives_commute hκ' hN' 0 1 z z

#print axioms transfer_diagonal
#print axioms derivative_diagonal
#print axioms transfer_derivatives_commute
#print axioms transfer_commutes_with_derivative

end QuantumNLS.LOCAL009Round50Diagonalization
