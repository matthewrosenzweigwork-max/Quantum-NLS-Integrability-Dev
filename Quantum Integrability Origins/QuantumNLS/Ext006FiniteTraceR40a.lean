import QuantumNLS.Ext006TracePowersR40a

/-! Exact finite matrix / actual reduced-density trace agreement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped InnerProductSpace ENNReal ComplexOrder
open Matrix
namespace QuantumNLS.Ext006FiniteTraceR40a
open TensorCarrier TraceClass Ext006PairDensityR40a Ext006CompressionR32a
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (b : HilbertBasis ℤ ℂ H) (S : Finset ℤ)

def matrixTensor (A : Matrix S S ℂ) : HilbertTensor ℂ H H :=
  ∑ i : S, ∑ j : S, A i j • htmul (b i) (b j)

def matrixOp (A : Matrix S S ℂ) : H →L[ℂ] H :=
  ∑ i : S, ∑ j : S, A i j • InnerProductSpace.rankOne ℂ (b i) (b j)

lemma contract_matrix_basis (A : Matrix S S ℂ) (i : S) :
    contract (b i) (matrixTensor b S A) = lift b S (fun j => A i j) := by
  classical
  simp [matrixTensor, lift, contract_htmul, orthonormal_iff_ite.mp b.orthonormal]

lemma contract_matrix_out (A : Matrix S S ℂ) (i : ℤ) (hi : i ∉ S) :
    contract (b i) (matrixTensor b S A) = 0 := by
  classical
  have hn : ∀ j : S, i ≠ (j : ℤ) := fun j h => hi (h.symm ▸ j.property)
  simp [matrixTensor, contract_htmul, orthonormal_iff_ite.mp b.orthonormal, hn]

omit [CompleteSpace H] in
lemma matrixOp_basis (A : Matrix S S ℂ) (i : S) :
    matrixOp b S A (b i) = lift b S (fun j => A j i) := by
  classical
  simp [matrixOp, lift, InnerProductSpace.rankOne_apply,
    orthonormal_iff_ite.mp b.orthonormal]

omit [CompleteSpace H] in
lemma matrixOp_out (A : Matrix S S ℂ) (i : ℤ) (hi : i ∉ S) :
    matrixOp b S A (b i) = 0 := by
  classical
  have hn : ∀ j : S, (j : ℤ) ≠ i := fun j h => hi (h ▸ j.property)
  simp [matrixOp, InnerProductSpace.rankOne_apply,
    orthonormal_iff_ite.mp b.orthonormal, hn]

omit [CompleteSpace H] in
lemma inner_lift (z w : S → ℂ) :
    inner ℂ (lift b S z) (lift b S w) = ∑ j : S, star (z j) * w j := by
  classical
  have hv : Orthonormal ℂ (fun i : S => b i) := b.orthonormal.comp _ Subtype.val_injective
  simp only [lift, sum_inner, inner_smul_left, hv.inner_right_fintype w, Complex.star_def]

omit [CompleteSpace H] in
lemma inner_basis_lift (z : S → ℂ) (i : S) : inner ℂ (b i) (lift b S z) = z i := by
  have hv : Orthonormal ℂ (fun i : S => b i) := b.orthonormal.comp _ Subtype.val_injective
  exact hv.inner_right_fintype z i

lemma density_matrix (A : Matrix S S ℂ) :
    reducedDensity (matrixTensor b S A) = matrixOp b S (A * Aᴴ) := by
  classical
  apply operator_ext_basis b
  intro i
  by_cases hi : i ∈ S
  · let ii : S := ⟨i,hi⟩
    apply b.repr.injective
    apply lp.ext
    funext j
    simp only [HilbertBasis.repr_apply_apply]
    rw [← inner_conj_symm (b j), density_inner,
      show b i = b ii from rfl, contract_matrix_basis]
    by_cases hj : j ∈ S
    · let jj : S := ⟨j,hj⟩
      rw [show b j = b jj from rfl, contract_matrix_basis, inner_lift,
        matrixOp_basis, inner_basis_lift]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul,
        starRingEnd_self_apply, Complex.star_def]
    · rw [contract_matrix_out b S A j hj, inner_zero_left, map_zero, matrixOp_basis]
      simp [lift, inner_sum, orthonormal_iff_ite.mp b.orthonormal,
        fun (k : S) => (show j ≠ (k : ℤ) from fun h => hj (h.symm ▸ k.property))]
  · rw [matrixOp_out b S _ i hi]
    apply ext_inner_right ℂ
    intro y
    rw [density_inner, contract_matrix_out b S A i hi, inner_zero_right, inner_zero_left]

omit [CompleteSpace H] in
lemma matrixOp_lift (A : Matrix S S ℂ) (z : S → ℂ) :
    matrixOp b S A (lift b S z) = lift b S (A *ᵥ z) := by
  classical
  simp only [lift, map_sum, map_smul, matrixOp_basis, lift, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_smul]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

omit [CompleteSpace H] in
lemma matrixOp_mul (A B : Matrix S S ℂ) :
    matrixOp b S (A*B) = matrixOp b S A * matrixOp b S B := by
  classical
  apply operator_ext_basis b
  intro i
  by_cases hi : i ∈ S
  · let ii : S := ⟨i,hi⟩
    rw [show b i = b ii from rfl, mul_apply_eq_comp,
      matrixOp_basis, matrixOp_basis, matrixOp_lift]
    rfl
  · simp [mul_apply_eq_comp, matrixOp_out b S _ i hi]

omit [CompleteSpace H] in
lemma matrixOp_power (A : Matrix S S ℂ) (n : ℕ) :
    matrixOp b S (A^(n+1)) = (matrixOp b S A)^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ A (n+1), matrixOp_mul, ih, pow_succ (matrixOp b S A) (n+1)]

lemma matrixOp_trace (A : Matrix S S ℂ) (hA : (matrixOp b S A).IsPositive) :
    traceNorm (matrixOp b S A) = ENNReal.ofReal (A.trace.re) := by
  classical
  rw [traceNorm_of_isPositive hA, posTrace_eq b hA, traceIn, tsum_eq_sum (s := S)]
  · rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [← Finset.sum_coe_sort S]
      simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [matrixOp_basis, inner_basis_lift]
      rfl
    · intro i hi
      exact hA.re_inner_nonneg_right (b i)
  · intro i hi
    simp [matrixOp_out b S _ i hi]

/-- The finite adjoint pair is the conjugate-transposed finite kernel matrix. -/
lemma finiteAdjointPair_eq (K : H →L[ℂ] H) :
    finiteAdjointPair b K S = matrixTensor b S ((Ext006CoreNorm.Km S (coordinates b K))ᴴ) := by
  classical
  rw [finiteAdjointPair, matrixTensor]
  simp only [← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [Matrix.conjTranspose_apply, Ext006CoreNorm.Km, Matrix.of_apply, coordinates,
    ContinuousLinearMap.adjoint_inner_right, inner_conj_symm, Complex.star_def]

/-- Exact all-power actual trace / compression-matrix equality. -/
theorem finite_density_trace_power (K : H →L[ℂ] H) (n : ℕ) :
    (traceNorm ((reducedDensity (finiteAdjointPair b K S))^(n+1))).toReal =
      (((Ext006CoreNorm.Tm S (coordinates b K))^(n+1)).trace).re := by
  classical
  have hd : reducedDensity (finiteAdjointPair b K S) =
      matrixOp b S (Ext006CoreNorm.Tm S (coordinates b K)) := by
    rw [finiteAdjointPair_eq, density_matrix, Matrix.conjTranspose_conjTranspose]
    rfl
  rw [hd, ← matrixOp_power, matrixOp_trace]
  · exact ENNReal.toReal_ofReal
      ((Ext006CoreLimit.trace_pow_nonneg_submul
        (Ext006CoreNorm.Tm_posSemidef S (coordinates b K)) (n+1) 0).1)
  · rw [matrixOp_power, ← hd]
    exact Ext006FredholmTracePower.trace_power_positive _ (reducedDensity_isPositive _) _

end QuantumNLS.Ext006FiniteTraceR40a

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006FiniteTraceR40a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round40a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
