import QuantumNLS.Ext006SymplecticKernel
import QuantumNLS.Fourier
import QuantumNLS.SymplecticBracket

/-!
FIN-CORE-BD-02, fixed-basis coordinate conjugation and HS kernel.
The conjugation is constructed from the supplied physical Hilbert basis.
The HS premise is on the actual antilinear block's complex representative;
the squeeze kernel, its symmetry and its trace-class square are conclusions.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext006KernelHilbertSchmidt
open Ext006Blocks Ext006SymplecticKernel TraceClass
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance 2000] InnerProductSpace.complexToReal

/-- Promote a genuinely complex-linear real map, without changing its action. -/
def complexify (T : H →L[ℝ] H) (hT : ∀ x, T (J x) = J (T x)) : H →L[ℂ] H where
  toFun := T
  map_add' := map_add T
  map_smul' := by
    intro c x
    rw [← Complex.re_add_im c]
    simp only [add_smul, mul_smul, Complex.coe_smul, map_add, map_smul]
    simpa only [RingHom.id_apply, mul_smul, Complex.coe_smul, J_apply] using
      congrArg (fun z => c.re • T x + c.im • z) (hT x)
  cont := T.continuous

omit [CompleteSpace H] in
@[simp] lemma complexify_apply (T : H →L[ℝ] H) (hT : ∀ x, T (J x) = J (T x)) (x : H) :
    complexify T hT x = T x := rfl

omit [CompleteSpace H] in
lemma complexify_norm (T : H →L[ℝ] H) (hT : ∀ x, T (J x) = J (T x)) :
    ‖complexify T hT‖ = ‖T‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) T.le_opNorm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (complexify T hT).le_opNorm

/-- Coefficientwise conjugation in the fixed basis, on the original H. -/
def conjugation (b : HilbertBasis ι ℂ H) : H →L[ℝ] H :=
  (b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) ∘L
    (starL' ℝ : lp (fun _ : ι => ℂ) 2 ≃L[ℝ] lp (fun _ : ι => ℂ) 2).toContinuousLinearMap ∘L
    (b.repr.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)

omit [CompleteSpace H] in
@[simp] lemma conjugation_apply (b : HilbertBasis ι ℂ H) (x : H) :
    conjugation b x = b.repr.symm (star (b.repr x)) := rfl

omit [CompleteSpace H] in
@[simp] lemma conjugation_sq (b : HilbertBasis ι ℂ H) (x : H) :
    conjugation b (conjugation b x) = x := by simp

omit [CompleteSpace H] in
@[simp] lemma conjugation_norm (b : HilbertBasis ι ℂ H) (x : H) :
    ‖conjugation b x‖ = ‖x‖ := by simp

omit [CompleteSpace H] in
@[simp] lemma conjugation_basis (b : HilbertBasis ι ℂ H) (i : ι) :
    conjugation b (b i) = b i := by
  classical
  apply b.repr.injective
  simp only [conjugation_apply, LinearIsometryEquiv.apply_symm_apply, b.repr_self]
  ext j
  by_cases h : j = i <;> simp [lp.single_apply, lp.star_apply, h]

omit [CompleteSpace H] in
lemma conjugation_J (b : HilbertBasis ι ℂ H) (x : H) :
    conjugation b (J x) = -J (conjugation b x) := by
  simp [conjugation_apply, J_apply, map_smul, star_smul]

/-- Complex representative of a real antilinear map, using this conjugation. -/
def antiRepresentative (b : HilbertBasis ι ℂ H) (T : H →L[ℝ] H)
    (hT : ∀ x, T (J x) = -J (T x)) : H →L[ℂ] H :=
  complexify (T ∘L conjugation b) (by
    intro x
    simp only [ContinuousLinearMap.comp_apply, conjugation_J, map_neg, hT, neg_neg])

omit [CompleteSpace H] in
@[simp] lemma antiRepresentative_apply (b : HilbertBasis ι ℂ H) (T : H →L[ℝ] H)
    (hT : ∀ x, T (J x) = -J (T x)) (x : H) :
    antiRepresentative b T hT x = T (conjugation b x) := rfl

omit [CompleteSpace H] in
lemma antiRepresentative_norm (b : HilbertBasis ι ℂ H) (T : H →L[ℝ] H)
    (hT : ∀ x, T (J x) = -J (T x)) : ‖antiRepresentative b T hT‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa only [antiRepresentative_apply, conjugation_norm] using T.le_opNorm (conjugation b x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa only [antiRepresentative_apply, conjugation_sq, conjugation_norm] using
      (antiRepresentative b T hT).le_opNorm (conjugation b x)

/-- The physical antilinear block in fixed-basis complex coordinates. -/
def beta (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H) : H →L[ℂ] H :=
  antiRepresentative b (antilinearPart S.toContinuousLinearMap)
    (antilinearPart_anticommutes_J S.toContinuousLinearMap)

/-- The squeeze kernel in the identical coordinates. -/
def squeeze (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H)
    (hS : Symplectic S.toContinuousLinearMap) : H →L[ℂ] H :=
  antiRepresentative b (kernel S hS) (kernel_anticommutes_J S hS)

/-- Conjugate of the constructed inverse complex block. -/
def inverseRepresentative (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H)
    (hS : Symplectic S.toContinuousLinearMap) : H →L[ℂ] H :=
  complexify (conjugation b ∘L (linearBlock S hS).symm.toContinuousLinearMap ∘L conjugation b) (by
    intro x
    change conjugation b ((linearBlock S hS).symm (conjugation b (J x))) =
      J (conjugation b ((linearBlock S hS).symm (conjugation b x)))
    simp only [conjugation_J, map_neg, linearBlock_inverse_J S hS, neg_neg])

lemma inverseRepresentative_norm_le (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H)
    (hS : Symplectic S.toContinuousLinearMap) : ‖inverseRepresentative b S hS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖conjugation b ((linearBlock S hS).symm (conjugation b x))‖ ≤ 1 * ‖x‖
  rw [conjugation_norm]
  have h := ((linearBlock S hS).symm.toContinuousLinearMap).le_opNorm (conjugation b x)
  rw [conjugation_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_right (linearBlock_inverse_norm_le S hS) (norm_nonneg x))

lemma squeeze_factorization (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H)
    (hS : Symplectic S.toContinuousLinearMap) :
    squeeze b S hS = beta b S ∘L inverseRepresentative b S hS := by
  ext x
  change antilinearPart S.toContinuousLinearMap ((linearBlock S hS).symm (conjugation b x)) =
    antilinearPart S.toContinuousLinearMap (conjugation b
      (conjugation b ((linearBlock S hS).symm (conjugation b x))))
  rw [conjugation_sq]

lemma squeeze_norm_lt_one (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H)
    (hS : Symplectic S.toContinuousLinearMap) : ‖squeeze b S hS‖ < 1 := by
  rw [squeeze, antiRepresentative_norm]
  exact kernel_norm_lt_one S hS

/-- Matrix symmetry, with no change to the physical complex structure. -/
lemma squeeze_matrix_symmetric (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H)
    (hS : Symplectic S.toContinuousLinearMap) (i j : ι) :
    inner ℂ (b i) (squeeze b S hS (b j)) = inner ℂ (b j) (squeeze b S hS (b i)) := by
  simp only [squeeze, antiRepresentative_apply, conjugation_basis]
  exact kernel_complex_symmetric S hS (b i) (b j)

/-- In particular the HS norm does not increase in forming the squeeze kernel. -/
lemma squeeze_hsSq_le (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H)
    (hS : Symplectic S.toContinuousLinearMap) : hsSq b (squeeze b S hS) ≤ hsSq b (beta b S) := by
  rw [squeeze_factorization, hsSq_eq_hsSq_adjoint b b, ContinuousLinearMap.adjoint_comp]
  have hi : ‖(inverseRepresentative b S hS).adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using inverseRepresentative_norm_le b S hS
  exact (hsSq_comp_le b hi (beta b S).adjoint).trans_eq (hsSq_eq_hsSq_adjoint b b (beta b S)).symm

/-- Full kernel clause of BD-02 for an arbitrary fixed physical Hilbert basis.
Only the original symplecticity and finite antilinear-block HS sum are inputs.
No implementer, covariance, squeeze existence, or determinant premise occurs. -/
theorem «FIN-CORE-BD-02-kernel» (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H)
    (hS : Symplectic S.toContinuousLinearMap) (hβ : hsSq b (beta b S) ≠ ⊤) :
    (∀ i j, inner ℂ (b i) (squeeze b S hS (b j)) = inner ℂ (b j) (squeeze b S hS (b i))) ∧
      ‖squeeze b S hS‖ < 1 ∧ hsSq b (squeeze b S hS) ≠ ⊤ ∧
      IsTraceClass ((squeeze b S hS).adjoint ∘L squeeze b S hS) ∧
      posTrace ((squeeze b S hS).adjoint ∘L squeeze b S hS) = hsSq b (squeeze b S hS) := by
  have hk := ne_top_of_le_ne_top hβ (squeeze_hsSq_le b S hS)
  exact ⟨squeeze_matrix_symmetric b S hS, squeeze_norm_lt_one b S hS, hk,
    Ext006Blocks.beta_adjoint_beta_traceClass b (squeeze b S hS) hk⟩

omit [CompleteSpace H] in
lemma beta_hsSq_eq_intrinsic (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H) :
    hsSq b (beta b S) = ∑' i, ENNReal.ofReal (‖antilinearPart S.toContinuousLinearMap (b i)‖^2) := by
  simp only [hsSq, beta, antiRepresentative_apply, conjugation_basis]

/-- Source section 4.1's P is the complex-linear projection of S. -/
def sourceP (S : H ≃L[ℝ] H) : H →L[ℂ] H :=
  complexify (complexPart S.toContinuousLinearMap) (complexPart_commutes_J S.toContinuousLinearMap)

/-- Source section 4.1's lower-left Q, with its stated conjugation convention. -/
def sourceQ (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H) : H →L[ℂ] H :=
  complexify (conjugation b ∘L antilinearPart S.toContinuousLinearMap) (by
    intro x
    simp only [ContinuousLinearMap.comp_apply, antilinearPart_anticommutes_J,
      map_neg, conjugation_J, neg_neg])

/-- The inverse of P, constructed from S rather than supplied. -/
def sourcePInv (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) : H →L[ℂ] H :=
  complexify (linearBlock S hS).symm.toContinuousLinearMap (by
    intro x
    change (linearBlock S hS).symm (J x) = J ((linearBlock S hS).symm x)
    exact linearBlock_inverse_J S hS x)

/-- Operator conjugation bar(T)=C T C in the fixed physical basis. -/
def operatorConjugate (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  complexify (conjugation b ∘L T.restrictScalars ℝ ∘L conjugation b) (by
    intro x
    change conjugation b (T (conjugation b (J x))) = J (conjugation b (T (conjugation b x)))
    have ht (z : H) : T (J z) = J (T z) := by simp [J_apply]
    simp only [conjugation_J, map_neg, ht, neg_neg])

lemma sourcePInv_left (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) (x : H) :
    sourcePInv S hS (sourceP S x) = x := by
  change (linearBlock S hS).symm (complexPart S.toContinuousLinearMap x) = x
  rw [← linearBlock_apply S hS, ContinuousLinearEquiv.symm_apply_apply]

lemma sourcePInv_right (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) (x : H) :
    sourceP S (sourcePInv S hS x) = x := by
  change complexPart S.toContinuousLinearMap ((linearBlock S hS).symm x) = x
  rw [← linearBlock_apply S hS, ContinuousLinearEquiv.apply_symm_apply]

omit [CompleteSpace H] in
/-- The upper component of R(f,Cf)=(P f + bar(Q) C f, ...). -/
lemma source_block_action (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H) (x : H) :
    S x = sourceP S x + conjugation b (sourceQ b S x) := by
  change S x = complexPart S.toContinuousLinearMap x +
    conjugation b (conjugation b (antilinearPart S.toContinuousLinearMap x))
  rw [conjugation_sq]
  exact (congrArg (fun T : H →L[ℝ] H => T x) (parts_sum S.toContinuousLinearMap)).symm

/-- Exact equation (4.1), including the bar over the entire product Q P^{-1}.
The bar is visible in the PDF and omitted by plain-text PDF extraction. -/
lemma sourceK_formula (b : HilbertBasis ι ℂ H) (S : H ≃L[ℝ] H)
    (hS : Symplectic S.toContinuousLinearMap) :
    squeeze b S hS = operatorConjugate b (sourceQ b S ∘L sourcePInv S hS) := by
  ext x
  change antilinearPart S.toContinuousLinearMap ((linearBlock S hS).symm (conjugation b x)) =
    conjugation b (conjugation b
      (antilinearPart S.toContinuousLinearMap ((linearBlock S hS).symm (conjugation b x))))
  rw [conjugation_sq]

section Physical
variable (L : ℝ) [Fact (0 < L)]
local instance physicalRealNormedSpace : NormedSpace ℝ (PhysicalTensor.L2T L) :=
  (InnerProductSpace.complexToReal : InnerProductSpace ℝ (PhysicalTensor.L2T L)).toNormedSpace

/-- The mass-L free Fourier basis, with the original physical complex structure. -/
def physicalBasis : HilbertBasis ℤ ℂ (PhysicalTensor.L2T L) :=
  HilbertBasis.ofRepr (Fourier.fourierL2 L)

/-- Kernel construction in the physical instance used before PROP-023.
The assumptions are precisely a physical bounded symplectic automorphism
and the HS condition on its constructed antilinear-block representative.
`beta_hsSq_eq_intrinsic` gives exactly the intrinsic basis-sum condition. -/
theorem «PROP-023-physical-kernel» (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : ∀ x y, SymplecticBracket.omega (S x) (S y) = SymplecticBracket.omega x y)
    (hβ : hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ K : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L,
      (∀ i j, inner ℂ (physicalBasis L i) (K (physicalBasis L j)) =
        inner ℂ (physicalBasis L j) (K (physicalBasis L i))) ∧
      ‖K‖ < 1 ∧ hsSq (physicalBasis L) K ≠ ⊤ ∧
      IsTraceClass (K.adjoint ∘L K) ∧ posTrace (K.adjoint ∘L K) = hsSq (physicalBasis L) K := by
  have hs : Symplectic S.toContinuousLinearMap := by
    intro x y
    have h := hS x y
    dsimp [SymplecticBracket.omega] at h
    change (inner ℂ (S x) (S y)).im = (inner ℂ x y).im
    linarith
  refine ⟨squeeze (physicalBasis L) S hs, ?_⟩
  apply «FIN-CORE-BD-02-kernel»
  exact hβ

end Physical
end QuantumNLS.Ext006KernelHilbertSchmidt

#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.complexify_apply
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.complexify_norm
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.conjugation_apply
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.conjugation_sq
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.conjugation_norm
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.conjugation_basis
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.conjugation_J
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.antiRepresentative_apply
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.antiRepresentative_norm
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.inverseRepresentative_norm_le
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.squeeze_factorization
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.squeeze_norm_lt_one
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.squeeze_matrix_symmetric
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.squeeze_hsSq_le
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.«FIN-CORE-BD-02-kernel»
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.beta_hsSq_eq_intrinsic
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.sourcePInv_left
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.sourcePInv_right
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.source_block_action
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.sourceK_formula
#print axioms QuantumNLS.Ext006KernelHilbertSchmidt.«PROP-023-physical-kernel»

-- COMPLETE NAMESPACE AUDIT
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006KernelHilbertSchmidt." then
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
  Lean.logInfo m!"Ext006KernelHilbertSchmidt audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
