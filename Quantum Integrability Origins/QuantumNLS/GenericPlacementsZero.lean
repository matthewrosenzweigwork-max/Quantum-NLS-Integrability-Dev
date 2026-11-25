/-
QuantumNLS.GenericPlacementsZero — the generic p=0 clause of DEF-041.

The zero-fold completed tensor power is identified with ℂ by the generic
zeroSectorIso construction.  The argument is independent of the one-particle
carrier: H need not be nonzero or complete.  In particular, the conclusion
also covers the zero Hilbert space and the N=0 placement.
-/
import QuantumNLS.TensorPlacements
import QuantumNLS.PhysicalTensor

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.PhysicalTensor

noncomputable section

namespace QuantumNLS.GenericPlacementsZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## The generic zero-particle sector is the scalars -/

/-- The zero-particle symmetric sector of an arbitrary complex inner-product
space is isometric to ℂ.  No nontriviality or completeness assumption on H is
needed: the zero-fold tensor power is ℂ even when H is the zero space. -/
def genericZeroSectorIso : SymSector ℂ H 0 ≃ₗᵢ[ℂ] ℂ := by
  let e : SymSector ℂ H 0 →ₗᵢ[ℂ] ℂ :=
    { toLinearMap :=
        (PhysicalTensor.zeroSectorIso :
          HilbertTensorPower ℂ H 0 ≃ₗᵢ[ℂ] ℂ).toLinearMap.comp
          (SymSector ℂ H 0).subtypeL.toLinearMap
      norm_map' := by
        intro x
        change ‖PhysicalTensor.zeroSectorIso (x : HilbertTensorPower ℂ H 0)‖ = ‖x‖
        rw [LinearIsometryEquiv.norm_map]
        rfl }
  exact LinearIsometryEquiv.ofSurjective e (by
    intro z
    refine ⟨⟨(PhysicalTensor.zeroSectorIso :
      HilbertTensorPower ℂ H 0 ≃ₗᵢ[ℂ] ℂ).symm z, ?_⟩, ?_⟩
    · rw [PhysicalTensor.symSector_zero]
      trivial
    · change PhysicalTensor.zeroSectorIso _ = z
      exact (PhysicalTensor.zeroSectorIso :
        HilbertTensorPower ℂ H 0 ≃ₗᵢ[ℂ] ℂ).apply_symm_apply z)

/-- The unique scalar represented by a bounded kernel on the zero-particle
sector, evaluated at the scalar unit under `genericZeroSectorIso`. -/
def zeroKernelScalar
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) : ℂ :=
  genericZeroSectorIso (H := H) (A ((genericZeroSectorIso (H := H)).symm 1))

/-- Every bounded operator on the generic zero-particle sector is precisely
multiplication by its scalar under `genericZeroSectorIso`. -/
theorem zeroKernel_eq_scalar_id
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) :
    A = zeroKernelScalar (H := H) A • ContinuousLinearMap.id ℂ _ := by
  let e := genericZeroSectorIso (H := H)
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
    _ = zeroKernelScalar (H := H) A • e x := by
      change (e x) * e (A (e.symm 1)) = e (A (e.symm 1)) * e x
      exact mul_comm _ _
    _ = e (zeroKernelScalar (H := H) A • x) := by rw [e.map_smul]

/-- Pointwise form of the scalar kernel characterization. -/
theorem zeroKernel_apply
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0)
    (x : SymSector ℂ H 0) :
    A x = zeroKernelScalar (H := H) A • x := by
  have h := congrArg (fun T : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0 => T x)
    (zeroKernel_eq_scalar_id (H := H) A)
  simpa using h

/-- The scalar characterization is exact: a proposed scalar represents `A`
if and only if it is the value determined by applying `A` to the scalar unit. -/
theorem zeroKernel_eq_scalar_id_iff
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) (c : ℂ) :
    A = c • ContinuousLinearMap.id ℂ _ ↔ c = zeroKernelScalar (H := H) A := by
  constructor
  · intro hA
    have h := congrArg
      (fun T : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0 =>
        genericZeroSectorIso (H := H) (T ((genericZeroSectorIso (H := H)).symm 1))) hA
    have hscalar : zeroKernelScalar (H := H) A = c := by
      simpa [zeroKernelScalar] using h
    exact hscalar.symm
  · intro hc
    rw [hc]
    exact zeroKernel_eq_scalar_id (H := H) A

/-- The zero scalar gives the zero bounded kernel, and conversely. -/
theorem zeroKernel_eq_zero_iff
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) :
    A = 0 ↔ zeroKernelScalar (H := H) A = 0 := by
  have hzero : (0 : ℂ) • ContinuousLinearMap.id ℂ (SymSector ℂ H 0) = 0 := by
    ext x
    simp
  constructor
  · intro hA
    have h' : A = (0 : ℂ) • ContinuousLinearMap.id ℂ _ := hA.trans hzero.symm
    exact ((zeroKernel_eq_scalar_id_iff (H := H) A 0).mp h').symm
  · intro hc
    have h' := (zeroKernel_eq_scalar_id_iff (H := H) A 0).mpr hc.symm
    exact h'.trans hzero

/-- The zero-extended generic kernel is its scalar times the identity on the
full zero-fold tensor power. -/
theorem extendSymKernel_zero_eq_scalar_id
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) :
    extendSymKernel A = zeroKernelScalar (H := H) A •
      ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H 0) := by
  ext x
  change (SymSector ℂ H 0).subtypeL (A (symProjToSector 0 x)) =
    zeroKernelScalar (H := H) A • x
  have hA := congrArg (fun T : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0 =>
      T (symProjToSector 0 x)) (zeroKernel_eq_scalar_id (H := H) A)
  rw [hA]
  simp [symProjToSector, PhysicalTensor.symProj_zero]

/-! ## Transport through the generic DEF-041 placement -/

/-- `htmap` sends identity operators on both factors to the identity on the
completed tensor product. -/
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

/-- In the zero-factor case, the first placement of a generic kernel is its
scalar multiple of the identity on the remaining tensor factors. -/
theorem firstPlacement_zero_eq_scalar_id {q : ℕ}
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) :
    firstPlacement (q := q) A = zeroKernelScalar (H := H) A •
      ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H (0 + q)) := by
  let e := splitIsometry (𝕜 := ℂ) (E := H) 0 q
  ext x
  apply e.injective
  change e (e.symm (htmap (extendSymKernel A)
      (ContinuousLinearMap.id ℂ _) (e x))) =
    e (zeroKernelScalar (H := H) A • x)
  rw [e.apply_symm_apply, extendSymKernel_zero_eq_scalar_id (H := H) A,
    htmap_smul_left, htmap_id_id, map_smul]
  rfl

/-- On the generic symmetric `(0+q)`-sector, the DEF-041 permutation average
at `p=0` is multiplication by the scalar represented by the zero-sector
kernel. This includes `q=0`. -/
theorem Q_N_0_eq_scalar_id_on_split (q : ℕ)
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) :
    Q_N_p (p := 0) (q := q) A =
      zeroKernelScalar (H := H) A •
        ContinuousLinearMap.id ℂ (SymSector ℂ H (0 + q)) := by
  calc
    Q_N_p (p := 0) (q := q) A =
        ((firstPlacement (q := q) A).comp
          (SymSector ℂ H (0 + q)).subtypeL).codRestrict
          (SymSector ℂ H (0 + q)) (by
            intro x
            rw [← symmetrizedPlacement_zero_eq_firstPlacement]
            exact symmetrizedPlacement_apply_mem A x) :=
      Q_N_0_eq_firstPlacement A
    _ = zeroKernelScalar (H := H) A •
        ContinuousLinearMap.id ℂ (SymSector ℂ H (0 + q)) := by
      apply ContinuousLinearMap.ext
      intro x
      apply Subtype.ext
      change firstPlacement (q := q) A x =
        zeroKernelScalar (H := H) A • x
      exact congrArg (fun T : HilbertTensorPower ℂ H (0 + q) →L[ℂ]
        HilbertTensorPower ℂ H (0 + q) => T x)
        (firstPlacement_zero_eq_scalar_id (H := H) A)

/-- The literal binomial subset average in DEF-041 has the same exact scalar
identity at `p=0`; here the sector is represented at total count `0+q`. -/
theorem Q_N_0_subsetAverage_eq_scalar_id (q : ℕ)
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) :
    ((subsetPlacementAverage (p := 0) (q := q) A).comp
      (SymSector ℂ H (0 + q)).subtypeL).codRestrict
        (SymSector ℂ H (0 + q)) (subsetPlacementAverage_apply_mem A) =
      zeroKernelScalar (H := H) A •
        ContinuousLinearMap.id ℂ (SymSector ℂ H (0 + q)) := by
  calc
    ((subsetPlacementAverage (p := 0) (q := q) A).comp
      (SymSector ℂ H (0 + q)).subtypeL).codRestrict
        (SymSector ℂ H (0 + q)) (subsetPlacementAverage_apply_mem A) =
      Q_N_p (p := 0) (q := q) A := (Q_N_p_eq_subsetPlacementAverage A).symm
    _ = zeroKernelScalar (H := H) A •
        ContinuousLinearMap.id ℂ (SymSector ℂ H (0 + q)) :=
      Q_N_0_eq_scalar_id_on_split (H := H) q A

/-- The `N=0, p=0` instance is included without a separate convention. -/
theorem Q_0_0_eq_scalar_id
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) :
    Q_N_p (p := 0) (q := 0) A = zeroKernelScalar (H := H) A •
      ContinuousLinearMap.id ℂ (SymSector ℂ H 0) := by
  simpa using Q_N_0_eq_scalar_id_on_split (H := H) 0 A

/-- Explicit zero-dimensional specialization: the DEF-041 `p=0` identity
also holds when the one-particle space itself is the bottom subspace of ℂ. -/
theorem zeroDimensional_Q_N_0_eq_scalar_id (q : ℕ)
    (A : SymSector ℂ (⊥ : Submodule ℂ ℂ) 0 →L[ℂ]
      SymSector ℂ (⊥ : Submodule ℂ ℂ) 0) :
    Q_N_p (H := (⊥ : Submodule ℂ ℂ)) (p := 0) (q := q) A =
      zeroKernelScalar (H := (⊥ : Submodule ℂ ℂ)) A •
        ContinuousLinearMap.id ℂ
          (SymSector ℂ (⊥ : Submodule ℂ ℂ) (0 + q)) :=
  Q_N_0_eq_scalar_id_on_split (H := (⊥ : Submodule ℂ ℂ)) q A

end QuantumNLS.GenericPlacementsZero

#print axioms QuantumNLS.GenericPlacementsZero.genericZeroSectorIso
#print axioms QuantumNLS.GenericPlacementsZero.zeroKernel_eq_scalar_id
#print axioms QuantumNLS.GenericPlacementsZero.zeroKernel_apply
#print axioms QuantumNLS.GenericPlacementsZero.zeroKernel_eq_scalar_id_iff
#print axioms QuantumNLS.GenericPlacementsZero.zeroKernel_eq_zero_iff
#print axioms QuantumNLS.GenericPlacementsZero.extendSymKernel_zero_eq_scalar_id
#print axioms QuantumNLS.GenericPlacementsZero.htmap_id_id
#print axioms QuantumNLS.GenericPlacementsZero.firstPlacement_zero_eq_scalar_id
#print axioms QuantumNLS.GenericPlacementsZero.Q_N_0_eq_scalar_id_on_split
#print axioms QuantumNLS.GenericPlacementsZero.Q_N_0_subsetAverage_eq_scalar_id
#print axioms QuantumNLS.GenericPlacementsZero.Q_0_0_eq_scalar_id
#print axioms QuantumNLS.GenericPlacementsZero.zeroDimensional_Q_N_0_eq_scalar_id
