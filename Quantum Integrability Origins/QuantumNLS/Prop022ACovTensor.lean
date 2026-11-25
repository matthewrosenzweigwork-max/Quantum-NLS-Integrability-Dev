import Mathlib
import QuantumNLS.Prop022GTensor
import QuantumNLS.IntrinsicContact
import QuantumNLS.TensorPlacements

/-! PROP-022 route A, stage A5a: generic tensor-level covariance under `U^{⊗n}`.

For a linear isometric equivalence `U : E ≃ₗᵢ[ℂ] F` of complex inner-product spaces:
* `split_tensorMap`: `split ∘ U^{⊗(k+m)} = (U^{⊗k} ⊗̂ U^{⊗m}) ∘ split`;
* `tensorMap_split_symm`: `U^{⊗(k+m)} (split⁻¹ (x ⊗ y)) = split⁻¹ (U^{⊗k}x ⊗ U^{⊗m}y)`;
* `tensorMap_symProj`, `symMap_orthProj`: the symmetrizing projection commutes with `U^{⊗n}`;
* `tensorMap_contractL`: contraction commutes with `U^{⊗}`;
* `tensorMap_extendSymKernel`, `tensorMap_firstPlacement`, `tensorMap_permutedPlacement`,
  `tensorMap_symmetrizedPlacement`: covariance of the placements of `TensorPlacements`. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace

namespace QuantumNLS.Prop022ACovTensor
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.IntrinsicContact

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- `U^{⊗n}` as a continuous linear map. -/
def tc (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) : HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ F n :=
  (tensorMap U n).toLinearIsometry.toContinuousLinearMap

@[simp] lemma tc_apply (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) (z : HilbertTensorPower ℂ E n) :
    tc U n z = tensorMap U n z := rfl

lemma tensorMap_ptprod_coe (U : E ≃ₗᵢ[ℂ] F) {n : ℕ} (f : Fin n → E) :
    tensorMap U n ((ptprod f : AlgTensorPower ℂ E n) : HilbertTensorPower ℂ E n) =
      ((ptprod (fun i => U (f i)) : AlgTensorPower ℂ F n) : HilbertTensorPower ℂ F n) := by
  rw [tensorMap_coe, algMap_ptprod]

/-- **Splitting commutes with `U^{⊗}`.** -/
theorem split_tensorMap (U : E ≃ₗᵢ[ℂ] F) (k m : ℕ) (z : HilbertTensorPower ℂ E (k + m)) :
    splitIsometry k m (tensorMap U (k + m) z) =
      htmap (tc U k) (tc U m) (splitIsometry k m z) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((splitIsometry k m).continuous.comp (tensorMap U (k + m)).continuous)
      ((htmap (tc U k) (tc U m)).continuous.comp (splitIsometry k m).continuous)
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      have key : ∀ g : Fin (k + m) → E,
          splitIsometry k m (tensorMap U (k + m) ((ptprod g : AlgTensorPower ℂ E (k + m)) :
            HilbertTensorPower ℂ E (k + m))) =
          htmap (tc U k) (tc U m) (splitIsometry k m ((ptprod g : AlgTensorPower ℂ E (k + m)) :
            HilbertTensorPower ℂ E (k + m))) := by
        intro g
        have hg : g = Fin.append (fun i => g (Fin.castAdd m i)) (fun i => g (Fin.natAdd k i)) :=
          (Fin.append_castAdd_natAdd (f := g)).symm
        set a : Fin k → E := fun i => g (Fin.castAdd m i)
        set b : Fin m → E := fun i => g (Fin.natAdd k i)
        rw [hg, tensorMap_ptprod_coe]
        have h2 : (fun i => U (Fin.append a b i)) =
            Fin.append (fun i => U (a i)) (fun i => U (b i)) := by
          funext i
          refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
        rw [h2, splitIsometry_ptprod_append, splitIsometry_ptprod_append, htmap_htmul,
          tc_apply, tc_apply, tensorMap_ptprod_coe, tensorMap_ptprod_coe]
      rw [UniformSpace.Completion.coe_smul]
      simp only [map_smul]
      rw [key f]
    | add x y hx hy =>
      rw [UniformSpace.Completion.coe_add]
      simp only [map_add]
      rw [hx, hy]

lemma htmap_tc_eq (U : E ≃ₗᵢ[ℂ] F) (k m : ℕ)
    (Φ : HilbertTensor ℂ (HilbertTensorPower ℂ E k) (HilbertTensorPower ℂ E m)) :
    htmap (tc U k) (tc U m) Φ =
      splitIsometry k m (tensorMap U (k + m) ((splitIsometry k m).symm Φ)) := by
  rw [split_tensorMap, LinearIsometryEquiv.apply_symm_apply]

lemma inner_htmap_tc (U : E ≃ₗᵢ[ℂ] F) (k m : ℕ)
    (Φ Ψ : HilbertTensor ℂ (HilbertTensorPower ℂ E k) (HilbertTensorPower ℂ E m)) :
    ⟪htmap (tc U k) (tc U m) Φ, htmap (tc U k) (tc U m) Ψ⟫_ℂ = ⟪Φ, Ψ⟫_ℂ := by
  rw [htmap_tc_eq, htmap_tc_eq, LinearIsometryEquiv.inner_map_map,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

theorem tensorMap_split_symm (U : E ≃ₗᵢ[ℂ] F) (k m : ℕ) (x : HilbertTensorPower ℂ E k)
    (y : HilbertTensorPower ℂ E m) :
    tensorMap U (k + m) ((splitIsometry k m).symm (htmul x y)) =
      (splitIsometry k m).symm (htmul (tensorMap U k x) (tensorMap U m y)) := by
  apply (splitIsometry k m).injective
  rw [split_tensorMap, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply,
    htmap_htmul]
  rfl

/-- The symmetrizing projection commutes with `U^{⊗n}`. -/
theorem tensorMap_symProj (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) (z : HilbertTensorPower ℂ E n) :
    tensorMap U n (symProj ℂ E n z) = symProj ℂ F n (tensorMap U n z) := by
  rw [symProj_eq_factorial_average, symProj_eq_factorial_average]
  simp only [smul_apply, sum_apply, map_smul, map_sum,
    permRep_apply]
  congr 1
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  exact (tensorMap_perm U σ z).symm

theorem symMap_orthProj (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) (z : HilbertTensorPower ℂ E n) :
    symMap U n ((SymSector ℂ E n).orthogonalProjectionOnto z) =
      (SymSector ℂ F n).orthogonalProjectionOnto (tensorMap U n z) := by
  apply Subtype.ext
  rw [symMap_coe]
  have h1 : ((SymSector ℂ E n).orthogonalProjectionOnto z : HilbertTensorPower ℂ E n) =
      symProj ℂ E n z := by
    rw [symProj_eq_starProjection]; rfl
  have h2 : ((SymSector ℂ F n).orthogonalProjectionOnto (tensorMap U n z) :
      HilbertTensorPower ℂ F n) = symProj ℂ F n (tensorMap U n z) := by
    rw [symProj_eq_starProjection]; rfl
  rw [h1, h2, tensorMap_symProj]

/-- Contraction with a first-slot vector commutes with `U^{⊗}`. -/
theorem tensorMap_contractL (U : E ≃ₗᵢ[ℂ] F) (k n : ℕ) (x : HilbertTensorPower ℂ E k)
    (w : HilbertTensorPower ℂ E (k + n)) :
    tensorMap U n (contractL (F := HilbertTensorPower ℂ E n) x (splitIsometry k n w)) =
      contractL (F := HilbertTensorPower ℂ F n) (tensorMap U k x)
        (splitIsometry k n (tensorMap U (k + n) w)) := by
  apply ext_inner_left ℂ
  intro y'
  obtain ⟨y, rfl⟩ := (tensorMap U n).surjective y'
  rw [inner_contractL, LinearIsometryEquiv.inner_map_map, inner_contractL, split_tensorMap]
  have h : htmul (tensorMap U k x) (tensorMap U n y) =
      htmap (tc U k) (tc U n) (htmul x y) := by rw [htmap_htmul]; rfl
  rw [h, inner_htmap_tc]

/-! ### Placements -/

theorem tensorMap_extendSymKernel (U : E ≃ₗᵢ[ℂ] F) {p : ℕ}
    (A : SymSector ℂ E p →L[ℂ] SymSector ℂ E p)
    (A' : SymSector ℂ F p →L[ℂ] SymSector ℂ F p)
    (hA : ∀ y, symMap U p (A y) = A' (symMap U p y)) (z : HilbertTensorPower ℂ E p) :
    tensorMap U p (TensorPlacements.extendSymKernel A z) =
      TensorPlacements.extendSymKernel A' (tensorMap U p z) := by
  have h : symMap U p (TensorPlacements.symProjToSector p z) =
      TensorPlacements.symProjToSector p (tensorMap U p z) := by
    apply Subtype.ext
    exact tensorMap_symProj U p z
  change ((symMap U p (A (TensorPlacements.symProjToSector p z)) : SymSector ℂ F p) :
      HilbertTensorPower ℂ F p) = ((A' (TensorPlacements.symProjToSector p (tensorMap U p z)) :
      SymSector ℂ F p) : HilbertTensorPower ℂ F p)
  rw [hA, h]

theorem tensorMap_firstPlacement (U : E ≃ₗᵢ[ℂ] F) {p q : ℕ}
    (A : SymSector ℂ E p →L[ℂ] SymSector ℂ E p)
    (A' : SymSector ℂ F p →L[ℂ] SymSector ℂ F p)
    (hA : ∀ y, symMap U p (A y) = A' (symMap U p y)) (z : HilbertTensorPower ℂ E (p + q)) :
    tensorMap U (p + q) (TensorPlacements.firstPlacement (q := q) A z) =
      TensorPlacements.firstPlacement (q := q) A' (tensorMap U (p + q) z) := by
  apply (splitIsometry p q).injective
  change splitIsometry p q (tensorMap U (p + q)
      ((splitIsometry p q).symm (htmap (TensorPlacements.extendSymKernel A)
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E q)) (splitIsometry p q z)))) =
    splitIsometry p q ((splitIsometry p q).symm (htmap (TensorPlacements.extendSymKernel A')
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ F q))
        (splitIsometry p q (tensorMap U (p + q) z))))
  rw [split_tensorMap, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply,
    split_tensorMap]
  have hcomp : ∀ Φ : HilbertTensor ℂ (HilbertTensorPower ℂ E p) (HilbertTensorPower ℂ E q),
      htmap (tc U p) (tc U q) (htmap (TensorPlacements.extendSymKernel A)
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E q)) Φ) =
      htmap (TensorPlacements.extendSymKernel A') (ContinuousLinearMap.id ℂ _)
        (htmap (tc U p) (tc U q) Φ) := by
    intro Φ
    have e1 := htmap_comp (tc U p) (TensorPlacements.extendSymKernel A) (tc U q)
      (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E q))
    have e2 := htmap_comp (TensorPlacements.extendSymKernel A') (tc U p)
      (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ F q)) (tc U q)
    have e3 : (tc U p).comp (TensorPlacements.extendSymKernel A) =
        (TensorPlacements.extendSymKernel A').comp (tc U p) := by
      ext w
      exact tensorMap_extendSymKernel U A A' hA w
    have e4 : (tc U q).comp (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E q)) =
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ F q)).comp (tc U q) := by
      ext w; rfl
    rw [e3, e4] at e1
    have := congrArg (fun T => T Φ) (e1.symm.trans e2)
    simpa using this
  exact hcomp _

theorem tensorMap_permutedPlacement (U : E ≃ₗᵢ[ℂ] F) {p q : ℕ} (σ : Equiv.Perm (Fin (p + q)))
    (A : SymSector ℂ E p →L[ℂ] SymSector ℂ E p)
    (A' : SymSector ℂ F p →L[ℂ] SymSector ℂ F p)
    (hA : ∀ y, symMap U p (A y) = A' (symMap U p y)) (z : HilbertTensorPower ℂ E (p + q)) :
    tensorMap U (p + q) (TensorPlacements.permutedPlacement σ A z) =
      TensorPlacements.permutedPlacement σ A' (tensorMap U (p + q) z) := by
  unfold TensorPlacements.permutedPlacement
  simp only [ContinuousLinearMap.comp_apply, permRep_apply]
  rw [← tensorMap_perm U σ, tensorMap_firstPlacement U A A' hA, ← tensorMap_perm U σ⁻¹]

theorem tensorMap_symmetrizedPlacement (U : E ≃ₗᵢ[ℂ] F) {p q : ℕ}
    (A : SymSector ℂ E p →L[ℂ] SymSector ℂ E p)
    (A' : SymSector ℂ F p →L[ℂ] SymSector ℂ F p)
    (hA : ∀ y, symMap U p (A y) = A' (symMap U p y)) (z : HilbertTensorPower ℂ E (p + q)) :
    tensorMap U (p + q) (TensorPlacements.symmetrizedPlacement (q := q) A z) =
      TensorPlacements.symmetrizedPlacement (q := q) A' (tensorMap U (p + q) z) := by
  unfold TensorPlacements.symmetrizedPlacement
  simp only [smul_apply, sum_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  exact tensorMap_permutedPlacement U σ A A' hA z

theorem symMap_Q_N_p (U : E ≃ₗᵢ[ℂ] F) {p q : ℕ}
    (A : SymSector ℂ E p →L[ℂ] SymSector ℂ E p)
    (A' : SymSector ℂ F p →L[ℂ] SymSector ℂ F p)
    (hA : ∀ y, symMap U p (A y) = A' (symMap U p y)) (y : SymSector ℂ E (p + q)) :
    symMap U (p + q) (TensorPlacements.Q_N_p (q := q) A y) =
      TensorPlacements.Q_N_p (q := q) A' (symMap U (p + q) y) := by
  apply Subtype.ext
  rw [symMap_coe]
  exact tensorMap_symmetrizedPlacement U A A' hA y.1

end QuantumNLS.Prop022ACovTensor

#print axioms QuantumNLS.Prop022ACovTensor.split_tensorMap
#print axioms QuantumNLS.Prop022ACovTensor.tensorMap_split_symm
#print axioms QuantumNLS.Prop022ACovTensor.symMap_orthProj
#print axioms QuantumNLS.Prop022ACovTensor.tensorMap_contractL
#print axioms QuantumNLS.Prop022ACovTensor.symMap_Q_N_p
