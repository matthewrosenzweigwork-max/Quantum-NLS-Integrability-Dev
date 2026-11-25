import QuantumNLS.KernelDefinition
import QuantumNLS.BethePhysicalTransfer

/-!
# R-C4F43CA8 Part (2), adjoint lemma: `(genericU_N_r N r hr A)† = genericU_N_r N r hr A†`

Derived from the placement definitions, no assumption:
* `symProj` is an orthogonal projection, hence selfadjoint (`symProj_adjoint`);
* `extendSymKernel A = subtypeL ∘ A ∘ symProjToSector` and `symProjToSector = subtypeL†` (accepted
  `BethePhysicalTransfer.symProjToSector_eq_adjoint`), so `(extendSymKernel A)† = extendSymKernel A†`;
* `firstPlacement A = e⁻¹ ∘ htmap(extendSymKernel A, 1) ∘ e` with `e` the splitting isometry; adjoints of the
  isometry equivalence are its inverse (`LinearIsometryEquiv.adjoint_eq_symm`) and `htmap` commutes with adjoints
  (`TensorCarrier.adjoint_htmap`);
* `sandwichPlacement A = P ∘ (firstPlacement A ∘ P)`, so its adjoint is `sandwichPlacement A†`;
* `U_N_r A` is the codRestriction of the sandwich, so `(U_N_r A)† = U_N_r A†` (inner-product identity);
* `genericU_N_r` is `castSymSectorOperator` of `U_N_r`, and transport along an equality commutes with adjoints.

Proved here (standard axioms only):
`symProj_adjoint`, `adjoint_extendSymKernel`, `adjoint_firstPlacement`, `adjoint_sandwichPlacement`,
`adjoint_U_N_r`, `castSym_adjoint`, `adjoint_genericU_N_r`.
Instances: `CompleteSpace (SymSector ℂ H p)` for a complete `H` (closed fixed-point set of `symProj`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators

namespace QuantumNLS.GenericUAdjoint

open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.BethePhysicalTransfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isClosed_symSector' (p : ℕ) :
    IsClosed ((SymSector ℂ H p : Submodule ℂ _) : Set (HilbertTensorPower ℂ H p)) := by
  have hset : ((SymSector ℂ H p : Submodule ℂ _) : Set (HilbertTensorPower ℂ H p)) =
      {x | symProj ℂ H p x = x} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_setOf_eq]
    rw [symProj_eq_starProjection p, Submodule.starProjection_eq_self_iff]
  rw [hset]
  exact isClosed_eq (symProj ℂ H p).continuous continuous_id

instance symSector_complete' (p : ℕ) : CompleteSpace (SymSector ℂ H p) :=
  (isClosed_symSector' (H := H) p).completeSpace_coe

theorem symProj_adjoint' (p : ℕ) :
    ContinuousLinearMap.adjoint (symProj ℂ H p) = symProj ℂ H p := by
  have h := (symProj_isStarProjection (𝕜 := ℂ) (E := H) p).isSelfAdjoint
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact h.star_eq

theorem adjoint_extendSymKernel {p : ℕ} (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    ContinuousLinearMap.adjoint (extendSymKernel A) = extendSymKernel (ContinuousLinearMap.adjoint A) := by
  unfold extendSymKernel
  rw [symProjToSector_eq_adjoint, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

/-- The adjoint of an isometry equivalence (as a continuous linear map) is its inverse. -/
theorem adjoint_iso {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (e : E ≃ₗᵢ[ℂ] F) :
    ContinuousLinearMap.adjoint (e.toLinearIsometry.toContinuousLinearMap) =
      e.symm.toLinearIsometry.toContinuousLinearMap := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  rw [LinearIsometryEquiv.inner_map_eq_flip e.symm x y, LinearIsometryEquiv.symm_symm]

theorem adjoint_firstPlacement {p q : ℕ} (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    ContinuousLinearMap.adjoint (firstPlacement (q := q) A) =
      firstPlacement (q := q) (ContinuousLinearMap.adjoint A) := by
  dsimp only [firstPlacement]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_iso, adjoint_iso, adjoint_htmap, ContinuousLinearMap.adjoint_id, adjoint_extendSymKernel]
  simp only [LinearIsometryEquiv.symm_symm, ContinuousLinearMap.comp_assoc]

theorem adjoint_sandwichPlacement {r q : ℕ} (A : BoundedSymmetricKernel H r) :
    ContinuousLinearMap.adjoint (sandwichPlacement (q := q) A) =
      sandwichPlacement (q := q) (ContinuousLinearMap.adjoint A) := by
  unfold sandwichPlacement
  simp only [ContinuousLinearMap.adjoint_comp, symProj_adjoint', adjoint_firstPlacement,
    ContinuousLinearMap.comp_assoc]

theorem adjoint_U_N_r {r q : ℕ} (A : BoundedSymmetricKernel H r) :
    ContinuousLinearMap.adjoint (U_N_r (r := r) (q := q) A) =
      U_N_r (r := r) (q := q) (ContinuousLinearMap.adjoint A) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  show ⟪sandwichPlacement (q := q) (ContinuousLinearMap.adjoint A) (x : HilbertTensorPower ℂ H (r + q)),
      (y : HilbertTensorPower ℂ H (r + q))⟫_ℂ =
    ⟪(x : HilbertTensorPower ℂ H (r + q)), sandwichPlacement (q := q) A (y : HilbertTensorPower ℂ H (r + q))⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_sandwichPlacement,
    ContinuousLinearMap.adjoint_adjoint]

theorem castSym_adjoint {m n : ℕ} (h : m = n) (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    ContinuousLinearMap.adjoint (QuantumNLS.KernelDefinition.castSymSectorOperator h A) =
      QuantumNLS.KernelDefinition.castSymSectorOperator h (ContinuousLinearMap.adjoint A) := by
  subst h
  rfl

/-- **Adjoint of the DEF-009 operator:** `(genericU_N_r N r hr A)† = genericU_N_r N r hr A†`. -/
theorem adjoint_genericU_N_r (N r : ℕ) (hr : r ≤ N) (A : BoundedSymmetricKernel H r) :
    ContinuousLinearMap.adjoint (genericU_N_r N r hr A) =
      genericU_N_r N r hr (ContinuousLinearMap.adjoint A) := by
  unfold genericU_N_r
  rw [castSym_adjoint, adjoint_U_N_r]

end QuantumNLS.GenericUAdjoint

#print axioms QuantumNLS.GenericUAdjoint.adjoint_genericU_N_r
#print axioms QuantumNLS.GenericUAdjoint.adjoint_U_N_r
#print axioms QuantumNLS.GenericUAdjoint.adjoint_firstPlacement
#print axioms QuantumNLS.GenericUAdjoint.adjoint_extendSymKernel
