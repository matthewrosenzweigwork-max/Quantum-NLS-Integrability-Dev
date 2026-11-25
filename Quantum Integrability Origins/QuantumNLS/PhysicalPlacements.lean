/-
QuantumNLS.PhysicalPlacements — physical realization of DEF-041.

Source: chapters/local/quantum_periods.tex:15–30.  The generic placement and
literal subset average are imported from the frozen TensorPlacements checkpoint
aec53164.  This module specializes them to the physical carrier L²(𝕋_L), writes
the particle count as N using p + (N-p) = N, and identifies the p=0 kernel
through PhysicalTensor.zeroSectorIso.
-/
import QuantumNLS.TensorPlacements
import QuantumNLS.PhysicalTensor

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.PhysicalTensor

noncomputable section

namespace QuantumNLS.PhysicalPlacements

/-! ## Scalar identification of the physical zero-particle kernel -/

variable (L : ℝ) [Fact (0 < L)]

/-- The physical zero-particle symmetric sector is isometric to ℂ, using the
zero-sector isometry from `PhysicalTensor` and the fact that every zero-sector
vector is symmetric. -/
def physZeroSectorIso :
    SymSector ℂ (L2T L) 0 ≃ₗᵢ[ℂ] ℂ := by
  let e : SymSector ℂ (L2T L) 0 →ₗᵢ[ℂ] ℂ :=
    { toLinearMap :=
        (PhysicalTensor.zeroSectorIso : HilbertTensorPower ℂ (L2T L) 0 ≃ₗᵢ[ℂ] ℂ).toLinearMap.comp
          (SymSector ℂ (L2T L) 0).subtypeL.toLinearMap
      norm_map' := by
        intro x
        change ‖PhysicalTensor.zeroSectorIso (x : HilbertTensorPower ℂ (L2T L) 0)‖ = ‖x‖
        rw [LinearIsometryEquiv.norm_map]
        rfl }
  exact LinearIsometryEquiv.ofSurjective e (by
    intro z
    refine ⟨⟨(PhysicalTensor.zeroSectorIso :
      HilbertTensorPower ℂ (L2T L) 0 ≃ₗᵢ[ℂ] ℂ).symm z, ?_⟩, ?_⟩
    · rw [PhysicalTensor.symSector_zero]
      trivial
    · change PhysicalTensor.zeroSectorIso _ = z
      exact (PhysicalTensor.zeroSectorIso :
        HilbertTensorPower ℂ (L2T L) 0 ≃ₗᵢ[ℂ] ℂ).apply_symm_apply z)

/-- The scalar represented by a bounded operator on the physical zero sector. -/
def zeroKernelScalar
    (A : SymSector ℂ (L2T L) 0 →L[ℂ] SymSector ℂ (L2T L) 0) : ℂ :=
  physZeroSectorIso L (A ((physZeroSectorIso L).symm 1))

/-- Every bounded operator on the physical zero-particle sector is multiplication
by its scalar under `PhysicalTensor.zeroSectorIso`. -/
theorem zeroKernel_eq_scalar_id
    (A : SymSector ℂ (L2T L) 0 →L[ℂ] SymSector ℂ (L2T L) 0) :
    A = zeroKernelScalar L A • ContinuousLinearMap.id ℂ _ := by
  let e := physZeroSectorIso L
  apply ContinuousLinearMap.ext
  intro x
  apply e.injective
  have hx : e.symm (e x) = (e x) • e.symm 1 := by
    apply e.injective
    simp
  calc
    e (A x) = e (A (e.symm (e x))) := by rw [e.symm_apply_apply]
    _ = e (A ((e x) • e.symm 1)) := by rw [hx]
    _ = e ((e x) • A (e.symm 1)) := by rw [map_smul]
    _ = (e x) • e (A (e.symm 1)) := by rw [e.map_smul]
    _ = zeroKernelScalar L A • e x := by
      change (e x) * e (A (e.symm 1)) = e (A (e.symm 1)) * e x
      exact mul_comm _ _
    _ = e (zeroKernelScalar L A • x) := by rw [e.map_smul]

/-- The zero-extended physical kernel is scalar multiplication on the full
zero-fold tensor power, since its symmetric sector is all of that space. -/
theorem extendSymKernel_zero_eq_scalar_id
    (A : SymSector ℂ (L2T L) 0 →L[ℂ] SymSector ℂ (L2T L) 0) :
    extendSymKernel A = zeroKernelScalar L A •
      ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ (L2T L) 0) := by
  ext x
  change (SymSector ℂ (L2T L) 0).subtypeL (A (symProjToSector 0 x)) =
    zeroKernelScalar L A • x
  have hA := congrArg (fun T : SymSector ℂ (L2T L) 0 →L[ℂ]
      SymSector ℂ (L2T L) 0 => T (symProjToSector 0 x))
      (zeroKernel_eq_scalar_id L A)
  rw [hA]
  simp [symProjToSector, PhysicalTensor.symProj_zero]

/-- `htmap` sends the two identity operators to the identity on the completed
tensor product. -/
theorem htmap_id_id {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] :
    htmap (ContinuousLinearMap.id ℂ X) (ContinuousLinearMap.id ℂ Y) =
      ContinuousLinearMap.id ℂ (HilbertTensor ℂ X Y) := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (htmap (ContinuousLinearMap.id ℂ X) (ContinuousLinearMap.id ℂ Y)).continuous
        (ContinuousLinearMap.id ℂ _).continuous
  | ih a =>
      simp [htmap, TensorProduct.mapL_id_id]

/-- In the zero-factor case, the first placement of a physical kernel is its
scalar multiple of the identity on the remaining tensor factors. -/
theorem firstPlacement_zero_eq_scalar_id {q : ℕ}
    (A : SymSector ℂ (L2T L) 0 →L[ℂ] SymSector ℂ (L2T L) 0) :
    firstPlacement (q := q) A = zeroKernelScalar L A •
      ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ (L2T L) (0 + q)) := by
  let e := splitIsometry (𝕜 := ℂ) (E := L2T L) 0 q
  ext x
  apply e.injective
  change e (e.symm (htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ _) (e x))) =
    e (zeroKernelScalar L A • x)
  rw [e.apply_symm_apply, extendSymKernel_zero_eq_scalar_id L A,
    htmap_smul_left, htmap_id_id, map_smul]
  rfl

/-! ## DEF-041 with source particle-count indexing -/

/-- Cast a symmetric-sector operator along an equality of particle counts. -/
def castSymSectorOperator {m n : ℕ} (h : m = n)
    (A : SymSector ℂ (L2T L) m →L[ℂ] SymSector ℂ (L2T L) m) :
    SymSector ℂ (L2T L) n →L[ℂ] SymSector ℂ (L2T L) n := by
  cases h
  exact A

/-- Casting scalar multiplication on a symmetric sector preserves its scalar
identity form. -/
theorem castSymSectorOperator_smul_id {m n : ℕ} (h : m = n) (c : ℂ) :
    castSymSectorOperator L h (c • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) m)) =
      c • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) n) := by
  cases h
  rfl

/-- The particle-count cast preserves operator norm. -/
theorem norm_castSymSectorOperator {m n : ℕ} (h : m = n)
    (A : SymSector ℂ (L2T L) m →L[ℂ] SymSector ℂ (L2T L) m) :
    ‖castSymSectorOperator L h A‖ = ‖A‖ := by
  cases h
  rfl

/-- The literal DEF-041 subset average on the physical N-particle sector.
The cast `p + (N-p) = N` makes the split used to define tensor placements
agree with the source's total particle count. -/
def physicalSubsetPlacementAverage (N p : ℕ) (hp : p ≤ N)
    (A : SymSector ℂ (L2T L) p →L[ℂ] SymSector ℂ (L2T L) p) :
    SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N := by
  let h : p + (N - p) = N := Nat.add_sub_of_le hp
  exact castSymSectorOperator L h
    (((subsetPlacementAverage (q := N - p) A).comp
      (SymSector ℂ (L2T L) (p + (N - p))).subtypeL).codRestrict
      (SymSector ℂ (L2T L) (p + (N - p)))
      (subsetPlacementAverage_apply_mem A))

/-- The restricted permutation-average definition of `Q_{N,p}` on the
physical N-particle sector. -/
def physicalQ_N_p (N p : ℕ) (hp : p ≤ N)
    (A : SymSector ℂ (L2T L) p →L[ℂ] SymSector ℂ (L2T L) p) :
    SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N := by
  let h : p + (N - p) = N := Nat.add_sub_of_le hp
  exact castSymSectorOperator L h (Q_N_p (q := N - p) A)

/-- The physical `Q_{N,p}` is exactly the literal binomial subset average in
DEF-041, at total particle count N. -/
theorem physicalQ_N_p_eq_subsetPlacementAverage (N p : ℕ) (hp : p ≤ N)
    (A : SymSector ℂ (L2T L) p →L[ℂ] SymSector ℂ (L2T L) p) :
    physicalQ_N_p L N p hp A = physicalSubsetPlacementAverage L N p hp A := by
  let h : p + (N - p) = N := Nat.add_sub_of_le hp
  change castSymSectorOperator L h (Q_N_p (q := N - p) A) =
    castSymSectorOperator L h
      (((subsetPlacementAverage (q := N - p) A).comp
        (SymSector ℂ (L2T L) (p + (N - p))).subtypeL).codRestrict
        (SymSector ℂ (L2T L) (p + (N - p)))
        (subsetPlacementAverage_apply_mem A))
  exact congrArg (castSymSectorOperator L h) (Q_N_p_eq_subsetPlacementAverage A)

/-- The physical DEF-041 average inherits the source's operator-norm bound. -/
theorem norm_physicalQ_N_p_le (N p : ℕ) (hp : p ≤ N)
    (A : SymSector ℂ (L2T L) p →L[ℂ] SymSector ℂ (L2T L) p) :
    ‖physicalQ_N_p L N p hp A‖ ≤ ‖A‖ := by
  let h : p + (N - p) = N := Nat.add_sub_of_le hp
  change ‖castSymSectorOperator L h (Q_N_p (q := N - p) A)‖ ≤ ‖A‖
  rw [norm_castSymSectorOperator]
  exact norm_Q_N_p_le A

/-! ## The p=0 scalar identity -/

/-- Before the outer particle-count cast, the p=0 placement restricted to its
symmetric sector is multiplication by the scalar of the zero-sector kernel. -/
theorem Q_N_0_eq_scalar_id_on_split (q : ℕ)
    (A : SymSector ℂ (L2T L) 0 →L[ℂ] SymSector ℂ (L2T L) 0) :
    Q_N_p (q := q) A = zeroKernelScalar L A •
      ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) (0 + q)) := by
  calc
    Q_N_p (q := q) A =
        ((firstPlacement (q := q) A).comp
          (SymSector ℂ (L2T L) (0 + q)).subtypeL).codRestrict
          (SymSector ℂ (L2T L) (0 + q)) (by
            intro x
            rw [← symmetrizedPlacement_zero_eq_firstPlacement]
            exact symmetrizedPlacement_apply_mem A x) :=
      Q_N_0_eq_firstPlacement A
    _ = zeroKernelScalar L A •
        ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) (0 + q)) := by
      apply ContinuousLinearMap.ext
      intro x
      apply Subtype.ext
      change firstPlacement (q := q) A x = zeroKernelScalar L A • x
      exact congrArg (fun T : HilbertTensorPower ℂ (L2T L) (0 + q) →L[ℂ]
        HilbertTensorPower ℂ (L2T L) (0 + q) => T x)
        (firstPlacement_zero_eq_scalar_id L A)

/-- At p=0, the literal DEF-041 subset average acts as the scalar represented
by the zero-sector kernel times the identity on the physical N-sector. -/
theorem physicalQ_N_0_eq_scalar_id (N : ℕ)
    (A : SymSector ℂ (L2T L) 0 →L[ℂ] SymSector ℂ (L2T L) 0) :
    physicalQ_N_p L N 0 (Nat.zero_le N) A =
      zeroKernelScalar L A • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) N) := by
  let h : 0 + (N - 0) = N := Nat.add_sub_of_le (Nat.zero_le N)
  change castSymSectorOperator L (Nat.add_sub_of_le (Nat.zero_le N))
      (Q_N_p (q := N - 0) A) =
    zeroKernelScalar L A • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) N)
  calc
    castSymSectorOperator L h (Q_N_p (q := N - 0) A) =
        castSymSectorOperator L h
          (zeroKernelScalar L A •
            ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) (0 + (N - 0)))) :=
      congrArg (castSymSectorOperator L h) (Q_N_0_eq_scalar_id_on_split L (N - 0) A)
    _ = zeroKernelScalar L A • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) N) :=
      castSymSectorOperator_smul_id L h (zeroKernelScalar L A)

end QuantumNLS.PhysicalPlacements

#print axioms QuantumNLS.PhysicalPlacements.physZeroSectorIso
#print axioms QuantumNLS.PhysicalPlacements.zeroKernel_eq_scalar_id
#print axioms QuantumNLS.PhysicalPlacements.extendSymKernel_zero_eq_scalar_id
#print axioms QuantumNLS.PhysicalPlacements.htmap_id_id
#print axioms QuantumNLS.PhysicalPlacements.firstPlacement_zero_eq_scalar_id
#print axioms QuantumNLS.PhysicalPlacements.castSymSectorOperator_smul_id
#print axioms QuantumNLS.PhysicalPlacements.norm_castSymSectorOperator
#print axioms QuantumNLS.PhysicalPlacements.Q_N_0_eq_scalar_id_on_split
#print axioms QuantumNLS.PhysicalPlacements.physicalQ_N_0_eq_scalar_id
#print axioms QuantumNLS.PhysicalPlacements.physicalSubsetPlacementAverage
#print axioms QuantumNLS.PhysicalPlacements.physicalQ_N_p_eq_subsetPlacementAverage
#print axioms QuantumNLS.PhysicalPlacements.norm_physicalQ_N_p_le
