import QuantumNLS.LOCAL009Round50Diagonalization
import QuantumNLS.HilbertDiagOp

/-! Operator-norm and Hermitian-part support for LOCAL-009. These general
lemmas do not claim that the printed contour operator has been constructed.
The imported physical diagonalization is the frozen round-50 input. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace QuantumNLS.LOCAL009R22OperatorSupport

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A scalar estimate uniform over a complete basis gives the same operator
norm estimate, with no finiteness or truncation of the basis index set. -/
theorem diagonal_error_norm (b : HilbertBasis ι ℂ H) (K A : H →L[ℂ] H)
    (k a : ι → ℂ) (hK : ∀ i, K (b i) = k i • b i)
    (hA : ∀ i, A (b i) = a i • b i) {C : ℝ} (hC : 0 ≤ C)
    (herr : ∀ i, ‖k i - a i‖ ≤ C) : ‖K-A‖ ≤ C := by
  classical
  obtain ⟨D, hD, hn⟩ := QuantumNLS.HilbertDiagOp.diag_exists b
    (fun i => k i - a i) C herr hC
  have heq : K-A = D := by
    ext v
    apply b.repr.injective
    apply lp.ext
    funext i
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, hD]
    change ⟪b i, K v - A v⟫_ℂ = _
    rw [inner_sub_right,
      QuantumNLS.HilbertDiagOp.eig_coeff b K k hK,
      QuantumNLS.HilbertDiagOp.eig_coeff b A a hA]
    ring
  rw [heq]
  exact hn

def hermitianPart (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (1/2 : ℂ) • (A + ContinuousLinearMap.adjoint A)

/-- Taking the Hermitian part preserves an approximation to a self-adjoint
operator with exactly the same constant. -/
theorem hermitian_error_le (K A : H →L[ℂ] H)
    (hK : ContinuousLinearMap.adjoint K = K) :
    ‖K - hermitianPart A‖ ≤ ‖K-A‖ := by
  have heq : K - hermitianPart A = (1/2 : ℂ) •
      ((K-A) + ContinuousLinearMap.adjoint (K-A)) := by
    simp only [hermitianPart, map_sub, hK]
    module
  rw [heq, norm_smul]
  have hhalf : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hhalf]
  have hn := norm_add_le (K-A) (ContinuousLinearMap.adjoint (K-A))
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  linarith

/-- Mean-field reparameterization of the frozen physical diagonalization
at the source's fixed coupling c=κ ε in sector N. -/
theorem fixed_coupling_transfer_diagonal
    {L κ ε : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (hε : 0 < ε)
    {N : ℕ} (hN : 0 < N) (z : ℂ) :
    QuantumNLS.NormalityBridge.IsDiag
      (QuantumNLS.LOCAL009Round50Diagonalization.physicalBetheBasis
        (show 0 < κ * ε * (N : ℝ) by positivity) hN)
      (QuantumNLS.NormalizedTransfer.normalizedTransfer L (κ * ε * N) N z) :=
  QuantumNLS.LOCAL009Round50Diagonalization.transfer_diagonal
    (show 0 < κ * ε * (N : ℝ) by positivity) hN z

theorem fixed_coupling_parameter {κ ε : ℝ} {N : ℕ} (hN : 0 < N) :
    (κ * ε * (N : ℝ)) / N = κ * ε := by
  have hn : (N : ℝ) ≠ 0 := by positivity
  field_simp

end QuantumNLS.LOCAL009R22OperatorSupport
#print axioms QuantumNLS.LOCAL009R22OperatorSupport.diagonal_error_norm
#print axioms QuantumNLS.LOCAL009R22OperatorSupport.hermitian_error_le
#print axioms QuantumNLS.LOCAL009R22OperatorSupport.fixed_coupling_transfer_diagonal
#print axioms QuantumNLS.LOCAL009R22OperatorSupport.fixed_coupling_parameter
