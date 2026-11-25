import QuantumNLS.BetheTransferOperators
import QuantumNLS.KernelDefinition

/-! Physical tensor placements and the literal transfer series from
periodic_basis.tex:326–339, with its adjoints at 375–394. The bounded kernels
are constructed from the actual ordered integral kernels in BTO1. The
falling factorial is (N)_m, with no extra m!. This module does not assume or
prove the Vlaar eigenvalue identity, completeness, or interacting orthogonality. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace QuantumNLS.BethePhysicalTransfer
open TensorCarrier TensorPlacements PhysicalTensor KernelDefinition
open BetheTransferKernelAdjoint BetheTransferOperators

section Placement
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The symmetric projection with subspace codomain is the adjoint inclusion. -/
theorem symProjToSector_eq_adjoint (m : ℕ) :
    symProjToSector (H := H) m = (SymSector ℂ H m).subtypeL.adjoint := by
  rw [Submodule.adjoint_subtypeL]
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change symProj ℂ H m x = ((SymSector ℂ H m).orthogonalProjectionOnto x : HilbertTensorPower ℂ H m)
  rw [Submodule.coe_orthogonalProjectionOnto_apply, symProj_eq_starProjection]

omit [CompleteSpace H] in
theorem extendSymKernel_adjoint {m : ℕ} (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    (extendSymKernel A).adjoint = extendSymKernel A.adjoint := by
  simp only [extendSymKernel, symProjToSector_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

theorem adjoint_isometryEquiv {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (e : E ≃ₗᵢ[ℂ] F) :
    e.toLinearIsometry.toContinuousLinearMap.adjoint =
      e.symm.toLinearIsometry.toContinuousLinearMap := e.adjoint_eq_symm

omit [CompleteSpace H] in
theorem firstPlacement_adjoint {m q : ℕ} (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    (firstPlacement (q := q) A).adjoint = firstPlacement (q := q) A.adjoint := by
  simp only [firstPlacement, ContinuousLinearMap.adjoint_comp,
    adjoint_isometryEquiv, LinearIsometryEquiv.symm_symm,
    adjoint_htmap, extendSymKernel_adjoint, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.comp_assoc]

omit [CompleteSpace H] in
theorem firstPlacement_smul {m q : ℕ} (c : ℂ)
    (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    firstPlacement (q := q) (c • A) = c • firstPlacement (q := q) A := by
  simp only [firstPlacement, extendSymKernel, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, htmap_smul_left]

/-- The physical normalized placement, written as the adjoint-inclusion
sandwich. This is the source P_N(A⊗1)P_N restricted to H_N. -/
def placement {m q : ℕ} (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    SymSector ℂ H (m+q) →L[ℂ] SymSector ℂ H (m+q) :=
  (SymSector ℂ H (m+q)).subtypeL.adjoint ∘L firstPlacement (q := q) A ∘L
    (SymSector ℂ H (m+q)).subtypeL

theorem placement_eq_U_N_r {m q : ℕ} (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    placement (q := q) A = U_N_r (q := q) A := by
  rw [U_N_r_eq_Q_N_p]
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change ((SymSector ℂ H (m+q)).subtypeL.adjoint (firstPlacement A x.1) :
    HilbertTensorPower ℂ H (m+q)) = symmetrizedPlacement A x.1
  rw [Submodule.adjoint_subtypeL, Submodule.coe_orthogonalProjectionOnto_apply,
    ← symProj_eq_starProjection]
  exact (symmetrizedPlacement_apply_symmetric A x).symm

omit [CompleteSpace H] in
theorem placement_adjoint {m q : ℕ} (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    (placement (q := q) A).adjoint = placement (q := q) A.adjoint := by
  simp only [placement, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, firstPlacement_adjoint,
    ContinuousLinearMap.comp_assoc]

omit [CompleteSpace H] in
theorem placement_smul {m q : ℕ} (c : ℂ) (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    placement (q := q) (c • A) = c • placement (q := q) A := by
  simp only [placement, firstPlacement_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul]

/-- Placement at a literal total particle count. -/
def totalPlacement (N m : ℕ) (hm : m ≤ N)
    (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  castSymSectorOperator (Nat.add_sub_of_le hm) (placement (q := N-m) A)

theorem totalPlacement_eq_genericU (N m : ℕ) (hm : m ≤ N)
    (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    totalPlacement N m hm A = genericU_N_r N m hm A := by
  simp only [totalPlacement, genericU_N_r, placement_eq_U_N_r]

omit [CompleteSpace H] in
theorem cast_adjoint {m n : ℕ} (h : m=n) (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    (castSymSectorOperator h A).adjoint = castSymSectorOperator h A.adjoint := by
  cases h
  rfl

omit [CompleteSpace H] in
theorem cast_smul {m n : ℕ} (h : m=n) (c : ℂ)
    (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    castSymSectorOperator h (c • A) = c • castSymSectorOperator h A := by
  cases h
  rfl

omit [CompleteSpace H] in
theorem totalPlacement_adjoint (N m : ℕ) (hm : m ≤ N)
    (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    (totalPlacement N m hm A).adjoint = totalPlacement N m hm A.adjoint := by
  simp only [totalPlacement, cast_adjoint, placement_adjoint]

omit [CompleteSpace H] in
theorem totalPlacement_smul (N m : ℕ) (hm : m ≤ N) (c : ℂ)
    (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    totalPlacement N m hm (c • A) = c • totalPlacement N m hm A := by
  simp only [totalPlacement, placement_smul, cast_smul]
end Placement

variable (L : ℝ) [Fact (0 < L)]

/-- The actual physical position representation of a symmetric tensor. -/
def positionInclusion (m : ℕ) : SymSector ℂ (L2T L) m →L[ℂ] L2TN L m :=
  (physUnitary : HilbertTensorPower ℂ (L2T L) m ≃ₗᵢ[ℂ] L2TN L m).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (SymSector ℂ (L2T L) m).subtypeL

/-- The completed physical symmetric tensor sector is exactly the symmetric
position L² space used by the frozen contact and Bethe eigenfamily modules. -/
def symmetricPosition (m : ℕ) : SymSector ℂ (L2T L) m ≃ₗᵢ[ℂ] ContactOperator.SymL2 L m where
  toFun v := ⟨physUnitary v.1, ContactOperator.mem_SymL2_iff _ |>.mpr
    ((mem_physSector_iff v.1).mp v.property)⟩
  invFun w := ⟨physUnitary.symm w.1, (mem_physSector_iff _).mpr (by
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (ContactOperator.mem_SymL2_iff _).mp w.property)⟩
  left_inv v := Subtype.ext (LinearIsometryEquiv.symm_apply_apply _ _)
  right_inv w := Subtype.ext (LinearIsometryEquiv.apply_symm_apply _ _)
  map_add' v w := Subtype.ext (map_add physUnitary v.1 w.1)
  map_smul' c v := Subtype.ext (map_smul physUnitary c v.1)
  norm_map' v := by
    change ‖(physUnitary : HilbertTensorPower ℂ (L2T L) m ≃ₗᵢ[ℂ] L2TN L m) v.1‖ = ‖v.1‖
    exact LinearIsometryEquiv.norm_map _ _

theorem positionInclusion_factor (m : ℕ) :
    positionInclusion L m = (ContactOperator.SymL2 L m).subtypeL ∘L
      (symmetricPosition L m).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- The literal ordered kernel compressed by the physical P_m, as a bounded
operator on the completed physical symmetric tensor sector. -/
def physicalKernel (m : ℕ) (z : ℂ) : BoundedSymmetricKernel (L2T L) m :=
  (positionInclusion L m).adjoint ∘L rawOperator L m z ∘L positionInclusion L m

/-- Exact carrier binding: the tensor kernel is the unitary transport of
the previously constructed compressed physical position operator. -/
theorem physicalKernel_eq_positionCompression (m : ℕ) (z : ℂ) :
    physicalKernel L m z =
      (symmetricPosition L m).toContinuousLinearEquiv.toContinuousLinearMap.adjoint ∘L
        compressedOperator L m z ∘L
          (symmetricPosition L m).toContinuousLinearEquiv.toContinuousLinearMap := by
  simp only [physicalKernel, positionInclusion_factor, compressedOperator,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

theorem physicalKernel_adjoint (m : ℕ) (z : ℂ) :
    (physicalKernel L m z).adjoint = adjointPhase L z • physicalKernel L m (conj z) := by
  simp only [physicalKernel, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, rawOperator_adjoint,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_assoc]

/-- Integral pairing of the actual physical compressed kernel. -/
theorem inner_physicalKernel (m : ℕ) (z : ℂ) (f g : SymSector ℂ (L2T L) m) :
    ⟪f, physicalKernel L m z g⟫_ℂ =
      ⟪positionInclusion L m f, rawOperator L m z (positionInclusion L m g)⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right (positionInclusion L m) f _

/-- The source degree-m transfer contribution, with exactly c^m(N)_m. -/
def transferTerm (N : ℕ) (c : ℝ) (z : ℂ) (m : Fin (N+1)) :
    SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N :=
  if 0 < m.val then
    ((c ^ m.val * N.descFactorial m.val : ℝ) : ℂ) •
      totalPlacement N m.val (Nat.le_of_lt_succ m.isLt) (physicalKernel L m.val z)
  else 0

/-- The literal bounded physical transfer from periodic_basis.tex:330–333. -/
def transfer (N : ℕ) (c : ℝ) (z : ℂ) :
    SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N :=
  (1 + Complex.exp (Complex.I * L * z)) • ContinuousLinearMap.id ℂ _ +
    ∑ m : Fin (N+1), transferTerm L N c z m

/-- Exact falling-factorial convention from the printed transfer. -/
theorem falling_factorial (N m : ℕ) (hm : m ≤ N) :
    N.descFactorial m = N.factorial / (N-m).factorial := Nat.descFactorial_eq_div hm

theorem transferTerm_adjoint (N : ℕ) (c : ℝ) (z : ℂ) (m : Fin (N+1)) :
    (transferTerm L N c z m).adjoint = adjointPhase L z • transferTerm L N c (conj z) m := by
  unfold transferTerm
  split_ifs
  · simp only [map_smulₛₗ, Complex.conj_ofReal, totalPlacement_adjoint,
      physicalKernel_adjoint, totalPlacement_smul, smul_smul]
    rw [mul_comm]
  · rw [map_zero]
    exact (smul_zero (adjointPhase L z)).symm

omit [Fact (0 < L)] in
/-- The scalar vacuum term has exactly the same phase adjoint as every kernel. -/
theorem scalar_adjoint (z : ℂ) :
    conj (1 + Complex.exp (Complex.I * L * z)) =
      adjointPhase L z * (1 + Complex.exp (Complex.I * L * conj z)) := by
  simp only [map_add, map_one, ← Complex.exp_conj, map_mul,
    Complex.conj_I, Complex.conj_ofReal, adjointPhase, mul_add, mul_one]
  have he : Complex.exp (-Complex.I * L * conj z) *
      Complex.exp (Complex.I * L * conj z) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    ring
  rw [he]
  ring

/-- Bounded physical transfer adjoint, including all normalized placements
and the vacuum term. This is R-99FDE9B6's displayed operator identity. -/
theorem transfer_adjoint (N : ℕ) (c : ℝ) (z : ℂ) :
    (transfer L N c z).adjoint = adjointPhase L z • transfer L N c (conj z) := by
  rw [transfer, map_add, map_smulₛₗ, scalar_adjoint, ContinuousLinearMap.adjoint_id, map_sum]
  simp only [transfer, transferTerm_adjoint, smul_add, smul_smul, Finset.smul_sum]

/-- The real half-phase gauge from the printed orthogonality argument. -/
def realTransfer (N : ℕ) (c a : ℝ) :
    SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N :=
  Complex.exp (-Complex.I * L * a / 2) • transfer L N c a

theorem realTransfer_adjoint (N : ℕ) (c a : ℝ) :
    (realTransfer L N c a).adjoint = realTransfer L N c a := by
  rw [realTransfer, map_smulₛₗ, transfer_adjoint]
  simp only [Complex.conj_ofReal, smul_smul, ← Complex.exp_conj,
    map_div₀, map_neg, Complex.conj_I, map_mul, map_ofNat,
    adjointPhase, ← Complex.exp_add]
  congr 2
  ring

theorem realTransfer_isSelfAdjoint (N : ℕ) (c a : ℝ) : IsSelfAdjoint (realTransfer L N c a) :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mpr (realTransfer_adjoint L N c a)

end QuantumNLS.BethePhysicalTransfer

#print axioms QuantumNLS.BethePhysicalTransfer.symProjToSector_eq_adjoint
#print axioms QuantumNLS.BethePhysicalTransfer.extendSymKernel_adjoint
#print axioms QuantumNLS.BethePhysicalTransfer.adjoint_isometryEquiv
#print axioms QuantumNLS.BethePhysicalTransfer.firstPlacement_adjoint
#print axioms QuantumNLS.BethePhysicalTransfer.firstPlacement_smul
#print axioms QuantumNLS.BethePhysicalTransfer.placement
#print axioms QuantumNLS.BethePhysicalTransfer.placement_eq_U_N_r
#print axioms QuantumNLS.BethePhysicalTransfer.placement_adjoint
#print axioms QuantumNLS.BethePhysicalTransfer.placement_smul
#print axioms QuantumNLS.BethePhysicalTransfer.totalPlacement
#print axioms QuantumNLS.BethePhysicalTransfer.totalPlacement_eq_genericU
#print axioms QuantumNLS.BethePhysicalTransfer.cast_adjoint
#print axioms QuantumNLS.BethePhysicalTransfer.cast_smul
#print axioms QuantumNLS.BethePhysicalTransfer.totalPlacement_adjoint
#print axioms QuantumNLS.BethePhysicalTransfer.totalPlacement_smul
#print axioms QuantumNLS.BethePhysicalTransfer.positionInclusion
#print axioms QuantumNLS.BethePhysicalTransfer.symmetricPosition
#print axioms QuantumNLS.BethePhysicalTransfer.positionInclusion_factor
#print axioms QuantumNLS.BethePhysicalTransfer.physicalKernel
#print axioms QuantumNLS.BethePhysicalTransfer.physicalKernel_eq_positionCompression
#print axioms QuantumNLS.BethePhysicalTransfer.physicalKernel_adjoint
#print axioms QuantumNLS.BethePhysicalTransfer.inner_physicalKernel
#print axioms QuantumNLS.BethePhysicalTransfer.transferTerm
#print axioms QuantumNLS.BethePhysicalTransfer.transfer
#print axioms QuantumNLS.BethePhysicalTransfer.falling_factorial
#print axioms QuantumNLS.BethePhysicalTransfer.transferTerm_adjoint
#print axioms QuantumNLS.BethePhysicalTransfer.scalar_adjoint
#print axioms QuantumNLS.BethePhysicalTransfer.transfer_adjoint
#print axioms QuantumNLS.BethePhysicalTransfer.realTransfer
#print axioms QuantumNLS.BethePhysicalTransfer.realTransfer_adjoint
#print axioms QuantumNLS.BethePhysicalTransfer.realTransfer_isSelfAdjoint

/- Dependency audit binds the transfer proof to the actual integral kernels,
compression, physical tensor realization, and normalized placements. -/
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BethePhysicalTransfer.transfer_adjoint,
    ``QuantumNLS.BethePhysicalTransfer.realTransfer_isSelfAdjoint,
    ``QuantumNLS.BethePhysicalTransfer.placement_eq_U_N_r,
    ``QuantumNLS.BethePhysicalTransfer.physicalKernel_eq_positionCompression,
    ``QuantumNLS.BethePhysicalTransfer.falling_factorial,
    ``QuantumNLS.BetheTransferOperators.inner_rawOperator,
    ``QuantumNLS.BetheTransferOperators.norm_rawOperator_le,
    ``QuantumNLS.BetheIntegralOperator.Kernel.operator_apply_ae]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheTransferKernelAdjoint.rawPlus,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawMinus,
      ``QuantumNLS.BetheTransferKernelAdjoint.PlusOrder,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawPlus_adjoint,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawMinus_adjoint,
      ``QuantumNLS.BetheTransferOperators.plusKernel,
      ``QuantumNLS.BetheTransferOperators.minusKernel,
      ``QuantumNLS.BetheTransferOperators.displacement_range,
      ``QuantumNLS.BetheIntegralOperator.Kernel.operator_adjoint,
      ``QuantumNLS.BetheIntegralOperator.Kernel.form_adjoint,
      ``QuantumNLS.BetheIntegralOperator.Kernel.operator_apply_ae,
      ``QuantumNLS.PhysicalTensor.physUnitary,
      ``QuantumNLS.ContactOperator.SymL2,
      ``QuantumNLS.BetheTransferOperators.compressedOperator,
      ``QuantumNLS.TensorPlacements.extendSymKernel,
      ``QuantumNLS.TensorPlacements.firstPlacement,
      ``QuantumNLS.TensorCarrier.adjoint_htmap,
      ``QuantumNLS.KernelDefinition.U_N_r,
      ``QuantumNLS.BethePhysicalTransfer.totalPlacement,
      ``QuantumNLS.BethePhysicalTransfer.scalar_adjoint,
      ``Nat.descFactorial] do
    unless seen.contains n do
      throwError "Physical transfer route missed source ingredient: {n}"
  Lean.logInfo m!"Physical-transfer route PASS: {seen.size} transitive constants; literal ordered kernels, actual integral action, bounded physical operators, both raw adjoints, physical P_m, tensor and normalized placements, exact falling factorial, vacuum term and real half-phase gauge reached. Vlaar eigenrelation and completeness remain unported."
