import Mathlib
import QuantumNLS.TensorCarrier

/-! PROP-022 general-scope transport, stage G1: the tensor-power and Fock functors of a unitary.

For a linear isometric equivalence `U : E ≃ₗᵢ[ℂ] F` of complex inner-product spaces this module builds
* `algMap U n` / `tensorMap U n`: `U^{⊗n}` on the algebraic and the completed Hilbert tensor power
  (`TensorCarrier.HilbertTensorPower`), with `U^{⊗n} (u^{⊗n}) = (U u)^{⊗n}`, functoriality
  (`trans`, `symm`) and commutation with every permutation unitary;
* `symMap U n`: its restriction `Sym^n E ≃ₗᵢ Sym^n F` to the symmetric sectors (`TensorCarrier.SymSector`);
* `FockSpace E = ℓ²(ℕ; Sym^n E)` (for `E = L2T L` this is the physical `Ext025B3PhysicalSectors.Fock L`,
  definitionally) and `fockMap U = Γ(U) : FockSpace E ≃ₗᵢ FockSpace F`, acting sector by sector.

Everything is generic in `E`, `F`: no basis, conjugation or carrier is fixed here. -/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

namespace QuantumNLS.Prop022GTensor
open QuantumNLS.TensorCarrier

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-! ### The algebraic tensor power map -/

/-- `U^{⊗n}` on the algebraic tensor power. -/
def algMap (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) : AlgTensorPower ℂ E n ≃ₗ[ℂ] AlgTensorPower ℂ F n :=
  PiTensorProduct.congr (fun _ : Fin n => U.toLinearEquiv)

theorem algMap_ptprod (U : E ≃ₗᵢ[ℂ] F) {n : ℕ} (f : Fin n → E) :
    algMap U n (ptprod f) = ptprod (fun i => U (f i)) :=
  PiTensorProduct.congr_tprod _ f

theorem inner_algMap (U : E ≃ₗᵢ[ℂ] F) {n : ℕ} (x y : AlgTensorPower ℂ E n) :
    ⟪algMap U n x, algMap U n y⟫_ℂ = ⟪x, y⟫_ℂ := by
  refine inner_map_map_of_span (algMap U n).toLinearMap (span_range_ptprod n) ?_ x y
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  rw [LinearEquiv.coe_toLinearMap, algMap_ptprod, algMap_ptprod, inner_ptprod, inner_ptprod]
  simp only [LinearIsometryEquiv.inner_map_map]

/-- `U^{⊗n}` as a linear isometric equivalence of the pre-Hilbert algebraic powers. -/
def algIso (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) : AlgTensorPower ℂ E n ≃ₗᵢ[ℂ] AlgTensorPower ℂ F n :=
  (algMap U n).isometryOfInner (inner_algMap U)

theorem algMap_trans (U : E ≃ₗᵢ[ℂ] F) (V : F ≃ₗᵢ[ℂ] G) {n : ℕ} (x : AlgTensorPower ℂ E n) :
    algMap (U.trans V) n x = algMap V n (algMap U n x) := by
  induction x using AlgTensorPower.induction_on with
  | smul_ptprod r f =>
    simp only [map_smul, algMap_ptprod, LinearIsometryEquiv.trans_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem algMap_symm_apply (U : E ≃ₗᵢ[ℂ] F) {n : ℕ} (x : AlgTensorPower ℂ F n) :
    algMap U n (algMap U.symm n x) = x := by
  induction x using AlgTensorPower.induction_on with
  | smul_ptprod r f =>
    simp only [map_smul, algMap_ptprod, LinearIsometryEquiv.apply_symm_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem algMap_perm (U : E ≃ₗᵢ[ℂ] F) {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : AlgTensorPower ℂ E n) :
    permLinearEquiv σ (algMap U n x) = algMap U n (permLinearEquiv σ x) := by
  induction x using AlgTensorPower.induction_on with
  | smul_ptprod r f =>
    simp only [map_smul, algMap_ptprod, permLinearEquiv_ptprod]
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ### The completed tensor power map -/

/-- `U^{⊗n}` on the completed Hilbert tensor power. -/
def tensorMap (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) :
    HilbertTensorPower ℂ E n ≃ₗᵢ[ℂ] HilbertTensorPower ℂ F n :=
  lieCompletion (algIso U n)

theorem tensorMap_coe (U : E ≃ₗᵢ[ℂ] F) {n : ℕ} (x : AlgTensorPower ℂ E n) :
    tensorMap U n (x : HilbertTensorPower ℂ E n) =
      ((algMap U n x : AlgTensorPower ℂ F n) : HilbertTensorPower ℂ F n) := by
  rw [tensorMap, lieCompletion_coe]
  rfl

/-- `U^{⊗n} u^{⊗n} = (U u)^{⊗n}`. -/
theorem tensorMap_htpow (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) (u : E) :
    tensorMap U n (htpow n u : HilbertTensorPower ℂ E n) = (htpow n (U u) : HilbertTensorPower ℂ F n) := by
  rw [htpow, tensorMap_coe, algMap_ptprod]
  rfl

theorem tensorMap_trans (U : E ≃ₗᵢ[ℂ] F) (V : F ≃ₗᵢ[ℂ] G) (n : ℕ) (z : HilbertTensorPower ℂ E n) :
    tensorMap (U.trans V) n z = tensorMap V n (tensorMap U n z) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (tensorMap (U.trans V) n).continuous
      ((tensorMap V n).continuous.comp (tensorMap U n).continuous)
  | ih a => rw [tensorMap_coe, tensorMap_coe, tensorMap_coe, algMap_trans]

theorem tensorMap_symm (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) (z : HilbertTensorPower ℂ F n) :
    tensorMap U.symm n z = (tensorMap U n).symm z := by
  rw [LinearIsometryEquiv.eq_symm_apply]
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((tensorMap U n).continuous.comp (tensorMap U.symm n).continuous)
      continuous_id
  | ih a => rw [tensorMap_coe, tensorMap_coe, algMap_symm_apply]

/-- `U^{⊗n}` commutes with every permutation unitary. -/
theorem tensorMap_perm (U : E ≃ₗᵢ[ℂ] F) {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : HilbertTensorPower ℂ E n) :
    permHilbertIsometry σ (tensorMap U n z) = tensorMap U n (permHilbertIsometry σ z) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((permHilbertIsometry σ).continuous.comp (tensorMap U n).continuous)
      ((tensorMap U n).continuous.comp (permHilbertIsometry σ).continuous)
  | ih a => rw [tensorMap_coe, permHilbertIsometry_coe, permHilbertIsometry_coe, tensorMap_coe, algMap_perm]

theorem tensorMap_mem (U : E ≃ₗᵢ[ℂ] F) {n : ℕ} {z : HilbertTensorPower ℂ E n}
    (hz : z ∈ SymSector ℂ E n) : tensorMap U n z ∈ SymSector ℂ F n := by
  change ∀ σ, (permRep ℂ F n σ : HilbertTensorPower ℂ F n →L[ℂ] HilbertTensorPower ℂ F n)
    (tensorMap U n z) = tensorMap U n z
  intro σ
  have h : (permRep ℂ E n σ : HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E n) z = z := hz σ
  rw [permRep_apply] at h ⊢
  rw [tensorMap_perm, h]

/-! ### The symmetric sectors -/

/-- `U^{⊗n}` restricted to `Sym^n E → Sym^n F`. -/
def symMap (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) : SymSector ℂ E n ≃ₗᵢ[ℂ] SymSector ℂ F n where
  toFun x := ⟨tensorMap U n (x : HilbertTensorPower ℂ E n), tensorMap_mem U x.2⟩
  invFun y := ⟨(tensorMap U n).symm (y : HilbertTensorPower ℂ F n), by rw [← tensorMap_symm]; exact tensorMap_mem U.symm y.2⟩
  map_add' x y := Subtype.ext (map_add (tensorMap U n) (x : HilbertTensorPower ℂ E n) y)
  map_smul' c x := Subtype.ext (map_smul (tensorMap U n) c (x : HilbertTensorPower ℂ E n))
  left_inv x := Subtype.ext ((tensorMap U n).symm_apply_apply (x : HilbertTensorPower ℂ E n))
  right_inv y := Subtype.ext ((tensorMap U n).apply_symm_apply (y : HilbertTensorPower ℂ F n))
  norm_map' x := (tensorMap U n).norm_map (x : HilbertTensorPower ℂ E n)

theorem symMap_coe (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) (x : SymSector ℂ E n) :
    ((symMap U n x : SymSector ℂ F n) : HilbertTensorPower ℂ F n) =
      tensorMap U n (x : HilbertTensorPower ℂ E n) := rfl

theorem symMap_symm (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) (y : SymSector ℂ F n) :
    symMap U.symm n y = (symMap U n).symm y :=
  Subtype.ext (tensorMap_symm U n (y : HilbertTensorPower ℂ F n))

/-! ### The Fock functor `Γ(U)` -/

variable (E) in
/-- Bosonic Fock space `⊕_{n ≥ 0} Sym^n E` (ℓ² direct sum). For `E = L2T L` this is, definitionally,
the physical `Ext025B3PhysicalSectors.Fock L`. -/
abbrev FockSpace := lp (fun n : ℕ => SymSector ℂ E n) 2

theorem memℓp_map (U : E ≃ₗᵢ[ℂ] F) (x : FockSpace E) :
    Memℓp (fun n => symMap U n (x n)) 2 := by
  have h : (fun n => ‖symMap U n (x n)‖) = fun n => ‖x n‖ :=
    funext fun n => (symMap U n).norm_map _
  rw [← memℓp_norm_iff, h, memℓp_norm_iff]
  exact x.2

/-- `Γ(U)` on vectors. -/
def fockFun (U : E ≃ₗᵢ[ℂ] F) (x : FockSpace E) : FockSpace F := ⟨fun n => symMap U n (x n), memℓp_map U x⟩

@[simp] theorem fockFun_apply (U : E ≃ₗᵢ[ℂ] F) (x : FockSpace E) (n : ℕ) :
    fockFun U x n = symMap U n (x n) := rfl

theorem norm_fockFun (U : E ≃ₗᵢ[ℂ] F) (x : FockSpace E) : ‖fockFun U x‖ = ‖x‖ := by
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow h2, lp.norm_eq_tsum_rpow h2]
  simp only [fockFun_apply, LinearIsometryEquiv.norm_map]

/-- **`Γ(U)`**, the second quantization of a unitary, acting sector by sector as `U^{⊗n}`. -/
def fockMap (U : E ≃ₗᵢ[ℂ] F) : FockSpace E ≃ₗᵢ[ℂ] FockSpace F where
  toFun := fockFun U
  invFun := fockFun U.symm
  map_add' x y := lp.ext (funext fun n => by
    simp only [fockFun_apply, lp.coeFn_add, Pi.add_apply, map_add])
  map_smul' c x := lp.ext (funext fun n => by
    simp only [fockFun_apply, lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply])
  left_inv x := lp.ext (funext fun n => by
    simp only [fockFun_apply, symMap_symm, LinearIsometryEquiv.symm_apply_apply])
  right_inv y := lp.ext (funext fun n => by
    simp only [fockFun_apply, symMap_symm, LinearIsometryEquiv.apply_symm_apply])
  norm_map' := norm_fockFun U

@[simp] theorem fockMap_apply (U : E ≃ₗᵢ[ℂ] F) (x : FockSpace E) (n : ℕ) :
    fockMap U x n = symMap U n (x n) := rfl

theorem fockMap_symm_apply (U : E ≃ₗᵢ[ℂ] F) (y : FockSpace F) (n : ℕ) :
    (fockMap U).symm y n = (symMap U n).symm (y n) := by
  change symMap U.symm n (y n) = _
  exact symMap_symm U n (y n)

theorem fockMap_trans (U : E ≃ₗᵢ[ℂ] F) (V : F ≃ₗᵢ[ℂ] G) (x : FockSpace E) :
    fockMap (U.trans V) x = fockMap V (fockMap U x) :=
  lp.ext (funext fun n => Subtype.ext (tensorMap_trans U V n (x n : HilbertTensorPower ℂ E n)))

/-- Number-sector norms are preserved: every spectral number observable is `Γ(U)`-invariant. -/
theorem norm_fockMap_sector (U : E ≃ₗᵢ[ℂ] F) (x : FockSpace E) (n : ℕ) :
    ‖fockMap U x n‖ = ‖x n‖ := (symMap U n).norm_map _

end QuantumNLS.Prop022GTensor

#print axioms QuantumNLS.Prop022GTensor.tensorMap_htpow
#print axioms QuantumNLS.Prop022GTensor.tensorMap_perm
#print axioms QuantumNLS.Prop022GTensor.symMap
#print axioms QuantumNLS.Prop022GTensor.fockMap
#print axioms QuantumNLS.Prop022GTensor.fockMap_trans
