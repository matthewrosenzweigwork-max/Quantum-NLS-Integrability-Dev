import QuantumNLS.LOCAL009R22LiteralScalar
import QuantumNLS.LOCAL009R22OperatorSupport
import QuantumNLS.RootMeasureTransfer

/-! Assembly on the actual complete physical Bethe basis. The approximant
has the literal scalar contour values as its diagonal entries. Identification
with a norm-valued integral built from the operator derivative of g_z(S(z))
is a separate obligation and is not asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Complex Set
open scoped InnerProductSpace
namespace QuantumNLS.LOCAL009R22Assembly
open QuantumNLS.BetheLabels QuantumNLS.LOCAL009R22LiteralScalar
  QuantumNLS.LOCAL009R22OperatorSupport QuantumNLS.HilbertDiagOp

theorem multiplicity_le {N : ℕ} (m : MArr N) (n : ℤ) : m.1 n ≤ N := by
  have hc := labelsEquivArr_apply (labelsEquivArr.symm m) n
  rw [labelsEquivArr.apply_symm_apply] at hc
  rw [hc]
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem scalarConstant_nonneg {κ L M : ℝ} (hκ : 0 < κ) (hL : 0 < L) (hM : 0 < M) :
    0 ≤ scalarConstant κ L M := by
  unfold scalarConstant halfWidth
    QuantumNLS.LOCAL009R22Integrand.integrandConstant
    QuantumNLS.LOCAL009R22Inverse.inverseRemainderConstant
    QuantumNLS.LOCAL009R22Inverse.displacementConstant
    QuantumNLS.LOCAL009R22Inverse.transferConstant
    QuantumNLS.LOCAL009R22Ratio.ratioBound
    QuantumNLS.LOCAL009R22Ratio.ratioLipschitz
  positivity

theorem eigen_of_coeff {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H) (a : ι → ℂ)
    (ha : ∀ i v, ⟪b i, A v⟫_ℂ = a i * ⟪b i, v⟫_ℂ) (i : ι) :
    A (b i) = a i • b i := by
  apply b.repr.injective
  apply lp.ext
  funext j
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, ha, inner_smul_right]
  by_cases he : j = i
  · subst j
    rfl
  · rw [b.orthonormal.inner_eq_zero he, mul_zero, mul_zero]

/-- A real diagonal approximation target is self-adjoint. -/
theorem selfAdjoint_of_real_diagonal {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H) (k : ι → ℝ)
    (hK : ∀ i, K (b i) = (k i : ℂ) • b i) :
    ContinuousLinearMap.adjoint K = K := by
  classical
  apply QuantumNLS.NormalityBridge.clm_ext_basis b
  intro i
  rw [QuantumNLS.RootMeasureTransfer.adjoint_diag b K (fun i => (k i : ℂ)) hK i, hK i]
  simp

/-- Actual physical-sector assembly of the scalar contour diagonal and the
scaled integer occupation diagonal, including the Hermitian-part estimate.
No scalar reconstruction estimate is a premise. -/
theorem actual_diagonal_assembly
    {κ L M ε : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (hM : 0 < M) (hsmall : κ*L*M ≤ 1/1000000)
    {N : ℕ} (hN : 0 < N) (hε : 0 < ε) (hεM : ε ≤ M)
    (hbudget : ε*N ≤ M) (n : ℤ) :
    let b := QuantumNLS.LOCAL009Round50Diagonalization.physicalBetheBasis
      (L := L) (show 0 < κ*ε*(N : ℝ) by positivity) hN
    ∃ K A : QuantumNLS.BetheCoefficientTransform.HN L N →L[ℂ]
        QuantumNLS.BetheCoefficientTransform.HN L N,
      (∀ m, K (b m) = ((ε : ℂ) * (m.1 n : ℂ)) • b m) ∧
      (∀ m, A (b m) = scalarA κ L M ε n (arrRoots L (κ*ε) m) • b m) ∧
      ContinuousLinearMap.adjoint K = K ∧
      ‖K-A‖ ≤ scalarConstant κ L M * ε^2 ∧
      ‖K-hermitianPart A‖ ≤ scalarConstant κ L M * ε^2 := by
  dsimp only
  let b := QuantumNLS.LOCAL009Round50Diagonalization.physicalBetheBasis
    (L := L) (show 0 < κ*ε*(N : ℝ) by positivity) hN
  let k : MArr N → ℂ := fun m => (ε : ℂ) * (m.1 n : ℂ)
  let a : MArr N → ℂ := fun m => scalarA κ L M ε n (arrRoots L (κ*ε) m)
  have hL : 0 < L := Fact.out
  have hC := scalarConstant_nonneg hκ hL hM
  have hknorm (m : MArr N) : ‖k m‖ ≤ M := by
    have hmn : (m.1 n : ℝ) ≤ N := by exact_mod_cast multiplicity_le m n
    have he : ‖k m‖ = ε * (m.1 n : ℝ) := by
      dsimp [k]
      simp [abs_of_pos hε]
    rw [he]
    exact (mul_le_mul_of_nonneg_left hmn hε.le).trans hbudget
  have herr (m : MArr N) : ‖a m-k m‖ ≤ scalarConstant κ L M * ε^2 :=
    actual_scalar_contour hκ hL hM hsmall hN hε hεM hbudget m n
  have hanorm (m : MArr N) : ‖a m‖ ≤ M + scalarConstant κ L M * ε^2 := by
    have ht := norm_add_le (a m-k m) (k m)
    rw [sub_add_cancel] at ht
    linarith [herr m, hknorm m]
  obtain ⟨K, hK, _⟩ := diag_exists b k M hknorm hM.le
  obtain ⟨A, hA, _⟩ := diag_exists b a (M + scalarConstant κ L M * ε^2) hanorm
    (by positivity)
  have hKe := eigen_of_coeff b K k hK
  have hAe := eigen_of_coeff b A a hA
  have hself : ContinuousLinearMap.adjoint K = K := by
    apply selfAdjoint_of_real_diagonal b K (fun m => ε * (m.1 n : ℝ))
    intro m
    simpa [k] using hKe m
  have hnorm : ‖K-A‖ ≤ scalarConstant κ L M * ε^2 := by
    apply diagonal_error_norm b K A k a hKe hAe (by positivity)
    intro m
    rw [norm_sub_rev]
    exact herr m
  exact ⟨K, A, hKe, hAe, hself, hnorm, (hermitian_error_le K A hself).trans hnorm⟩

end QuantumNLS.LOCAL009R22Assembly
#print axioms QuantumNLS.LOCAL009R22Assembly.multiplicity_le
#print axioms QuantumNLS.LOCAL009R22Assembly.scalarConstant_nonneg
#print axioms QuantumNLS.LOCAL009R22Assembly.eigen_of_coeff
#print axioms QuantumNLS.LOCAL009R22Assembly.selfAdjoint_of_real_diagonal
#print axioms QuantumNLS.LOCAL009R22Assembly.actual_diagonal_assembly
