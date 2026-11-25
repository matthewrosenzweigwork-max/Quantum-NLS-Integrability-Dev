import Mathlib
import QuantumNLS.Prop022GTensor

/-! PROP-022 route A, finite-dimensional case, stage B1: the tensor-power and Fock functors of a
linear ISOMETRY `J : E →ₗᵢ[ℂ] F` (not nec. surjective).

* `tensorMapI J n : E^{⊗̂n} →ₗᵢ F^{⊗̂n}` with `J^{⊗n} (u^{⊗n}) = (J u)^{⊗n}`, commuting with permutations;
* `symMapI J n : Sym^n E →ₗᵢ Sym^n F`;
* `fockMapI J = Γ(J) : FockSpace E →ₗᵢ FockSpace F`;
* for a unitary `U`, `tensorMapI U.toLinearIsometry = tensorMap U` (compatibility with `Prop022GTensor`). -/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

namespace QuantumNLS.Prop022AIsoTensor
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- `J^{⊗n}` on the algebraic tensor power. -/
def algMapI (J : E →ₗᵢ[ℂ] F) (n : ℕ) : AlgTensorPower ℂ E n →ₗ[ℂ] AlgTensorPower ℂ F n :=
  PiTensorProduct.map (fun _ : Fin n => J.toLinearMap)

theorem algMapI_ptprod (J : E →ₗᵢ[ℂ] F) {n : ℕ} (f : Fin n → E) :
    algMapI J n (ptprod f) = ptprod (fun i => J (f i)) :=
  PiTensorProduct.map_tprod _ f

theorem inner_algMapI (J : E →ₗᵢ[ℂ] F) {n : ℕ} (x y : AlgTensorPower ℂ E n) :
    ⟪algMapI J n x, algMapI J n y⟫_ℂ = ⟪x, y⟫_ℂ := by
  refine inner_map_map_of_span (algMapI J n) (span_range_ptprod n) ?_ x y
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  rw [algMapI_ptprod, algMapI_ptprod, inner_ptprod, inner_ptprod]
  simp only [LinearIsometry.inner_map_map]

/-- `J^{⊗n}` as a linear isometry of the pre-Hilbert algebraic powers. -/
def algIsoI (J : E →ₗᵢ[ℂ] F) (n : ℕ) : AlgTensorPower ℂ E n →ₗᵢ[ℂ] AlgTensorPower ℂ F n :=
  (algMapI J n).isometryOfInner (inner_algMapI J)

/-- `J^{⊗n}` on the completed Hilbert tensor power. -/
def tensorMapI (J : E →ₗᵢ[ℂ] F) (n : ℕ) : HilbertTensorPower ℂ E n →ₗᵢ[ℂ] HilbertTensorPower ℂ F n :=
  (algIsoI J n).completion

theorem tensorMapI_coe (J : E →ₗᵢ[ℂ] F) {n : ℕ} (x : AlgTensorPower ℂ E n) :
    tensorMapI J n (x : HilbertTensorPower ℂ E n) =
      ((algMapI J n x : AlgTensorPower ℂ F n) : HilbertTensorPower ℂ F n) := by
  rw [tensorMapI, LinearIsometry.completion_apply_coe]
  rfl

theorem tensorMapI_htpow (J : E →ₗᵢ[ℂ] F) (n : ℕ) (u : E) :
    tensorMapI J n (htpow n u : HilbertTensorPower ℂ E n) =
      (htpow n (J u) : HilbertTensorPower ℂ F n) := by
  rw [htpow, tensorMapI_coe, algMapI_ptprod]
  rfl

theorem tensorMapI_perm (J : E →ₗᵢ[ℂ] F) {n : ℕ} (σ : Equiv.Perm (Fin n))
    (z : HilbertTensorPower ℂ E n) :
    permHilbertIsometry σ (tensorMapI J n z) = tensorMapI J n (permHilbertIsometry σ z) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((permHilbertIsometry σ).continuous.comp (tensorMapI J n).continuous)
      ((tensorMapI J n).continuous.comp (permHilbertIsometry σ).continuous)
  | ih a =>
    have h : ∀ y : AlgTensorPower ℂ E n, permLinearEquiv σ (algMapI J n y) =
        algMapI J n (permLinearEquiv σ y) := by
      intro y
      induction y using AlgTensorPower.induction_on with
      | smul_ptprod r f => simp only [map_smul, algMapI_ptprod, permLinearEquiv_ptprod]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [tensorMapI_coe, permHilbertIsometry_coe, permHilbertIsometry_coe, tensorMapI_coe, h]

theorem tensorMapI_mem (J : E →ₗᵢ[ℂ] F) {n : ℕ} {z : HilbertTensorPower ℂ E n}
    (hz : z ∈ SymSector ℂ E n) : tensorMapI J n z ∈ SymSector ℂ F n := by
  change ∀ σ, (permRep ℂ F n σ : HilbertTensorPower ℂ F n →L[ℂ] HilbertTensorPower ℂ F n)
    (tensorMapI J n z) = tensorMapI J n z
  intro σ
  have h : (permRep ℂ E n σ : HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E n) z = z := hz σ
  rw [permRep_apply] at h ⊢
  rw [tensorMapI_perm, h]

/-- `J^{⊗n}` restricted to the symmetric sectors. -/
def symMapI (J : E →ₗᵢ[ℂ] F) (n : ℕ) : SymSector ℂ E n →ₗᵢ[ℂ] SymSector ℂ F n where
  toFun x := ⟨tensorMapI J n (x : HilbertTensorPower ℂ E n), tensorMapI_mem J x.2⟩
  map_add' x y := Subtype.ext (map_add (tensorMapI J n) (x : HilbertTensorPower ℂ E n) y)
  map_smul' c x := Subtype.ext (map_smul (tensorMapI J n) c (x : HilbertTensorPower ℂ E n))
  norm_map' x := (tensorMapI J n).norm_map (x : HilbertTensorPower ℂ E n)

theorem symMapI_coe (J : E →ₗᵢ[ℂ] F) (n : ℕ) (x : SymSector ℂ E n) :
    ((symMapI J n x : SymSector ℂ F n) : HilbertTensorPower ℂ F n) =
      tensorMapI J n (x : HilbertTensorPower ℂ E n) := rfl

theorem memℓp_mapI (J : E →ₗᵢ[ℂ] F) (x : FockSpace E) :
    Memℓp (fun n => symMapI J n (x n)) 2 := by
  have h : (fun n => ‖symMapI J n (x n)‖) = fun n => ‖x n‖ :=
    funext fun n => (symMapI J n).norm_map _
  rw [← memℓp_norm_iff, h, memℓp_norm_iff]
  exact x.2

/-- **`Γ(J)`**, the second quantization of an isometry. -/
def fockMapI (J : E →ₗᵢ[ℂ] F) : FockSpace E →ₗᵢ[ℂ] FockSpace F where
  toFun x := ⟨fun n => symMapI J n (x n), memℓp_mapI J x⟩
  map_add' x y := lp.ext (funext fun n => by
    simp only [lp.coeFn_add, Pi.add_apply, map_add])
  map_smul' c x := lp.ext (funext fun n => by
    simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply])
  norm_map' x := by
    have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    show ‖(⟨fun n => symMapI J n (x n), memℓp_mapI J x⟩ : FockSpace F)‖ = ‖x‖
    rw [lp.norm_eq_tsum_rpow h2, lp.norm_eq_tsum_rpow h2]
    simp only [LinearIsometry.norm_map]

@[simp] theorem fockMapI_apply (J : E →ₗᵢ[ℂ] F) (x : FockSpace E) (n : ℕ) :
    fockMapI J x n = symMapI J n (x n) := rfl

/-- Compatibility with the unitary functor of `Prop022GTensor`. -/
theorem tensorMapI_equiv (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) (z : HilbertTensorPower ℂ E n) :
    tensorMapI U.toLinearIsometry n z = tensorMap U n z := by
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (tensorMapI U.toLinearIsometry n).continuous (tensorMap U n).continuous
  | ih a =>
    rw [tensorMapI_coe, tensorMap_coe]
    congr 1

theorem fockMapI_equiv (U : E ≃ₗᵢ[ℂ] F) (x : FockSpace E) :
    fockMapI U.toLinearIsometry x = fockMap U x :=
  lp.ext (funext fun n => Subtype.ext (tensorMapI_equiv U n (x n : HilbertTensorPower ℂ E n)))

/-- Functoriality `Γ(K ∘ J) = Γ(K) Γ(J)` for isometries. -/
theorem fockMapI_comp (J : E →ₗᵢ[ℂ] F) (K : F →ₗᵢ[ℂ] G) (x : FockSpace E) :
    fockMapI (K.comp J) x = fockMapI K (fockMapI J x) := by
  apply lp.ext
  funext n
  apply Subtype.ext
  change tensorMapI (K.comp J) n (x n : HilbertTensorPower ℂ E n) =
    tensorMapI K n (tensorMapI J n (x n : HilbertTensorPower ℂ E n))
  generalize (x n : HilbertTensorPower ℂ E n) = z
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (tensorMapI (K.comp J) n).continuous
      ((tensorMapI K n).continuous.comp (tensorMapI J n).continuous)
  | ih a =>
    rw [tensorMapI_coe, tensorMapI_coe, tensorMapI_coe]
    congr 1
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f => simp only [map_smul, algMapI_ptprod]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]

end QuantumNLS.Prop022AIsoTensor

#print axioms QuantumNLS.Prop022AIsoTensor.tensorMapI_htpow
#print axioms QuantumNLS.Prop022AIsoTensor.symMapI
#print axioms QuantumNLS.Prop022AIsoTensor.fockMapI
#print axioms QuantumNLS.Prop022AIsoTensor.fockMapI_equiv
#print axioms QuantumNLS.Prop022AIsoTensor.fockMapI_comp
