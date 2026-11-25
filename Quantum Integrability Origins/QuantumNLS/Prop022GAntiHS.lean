import Mathlib
import QuantumNLS.Ext006KernelHilbertSchmidt

/-! PROP-022 general-scope transport, stage G3a: basis-free Hilbert--Schmidt norm of an
antilinear operator, and unitary transport of real-linear operators.

On a general complex Hilbert space there is no canonical conjugation, so the printed
`‖β‖_HS` of the antilinear block `β = (S + iSi)/2` (fluctuations.tex:127-130) is read
intrinsically as `∑ᵢ ‖β eᵢ‖²` over an orthonormal basis `e`.  This module proves:

* `antiHS_basis_indep`: for an antilinear bounded real-linear `T` the sum `∑ᵢ ‖T eᵢ‖²` is
  the same for every Hilbert basis (any index types);
* `pull U T = U⁻¹ ∘ T ∘ U` for a unitary `U : H ≃ₗᵢ[ℂ] F`: norm, complex-linear part,
  antilinear part, and the intrinsic HS sum are transported (`antiHS_pull`);
* `antiHS_eq_hsSq_beta`: in a fixed basis the intrinsic sum is the frozen
  `hsSq b (beta b S)` of EXT-006 (so the frozen torus statements are instances). -/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace QuantumNLS.Prop022GAntiHS
open Ext006Blocks

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
attribute [local instance 2000] InnerProductSpace.complexToReal

/-- Antilinearity in the `Ext006Blocks` form. -/
def Antilinear (T : F →L[ℝ] F) : Prop := ∀ x, T (J x) = -J (T x)

/-- Complex-linearity in the `Ext006Blocks` form. -/
def CLinear (T : F →L[ℝ] F) : Prop := ∀ x, T (J x) = J (T x)

lemma anti_smul {T : F →L[ℝ] F} (hT : Antilinear T) (a : ℂ) (x : F) :
    T (a • x) = (conj a) • T x := by
  have hx : a • x = (a.re : ℝ) • x + (a.im : ℝ) • J x := by
    rw [J_apply, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul,
      Complex.re_add_im]
  have hc : conj a = (a.re : ℂ) - (a.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hx, map_add, map_smul, map_smul, hT, J_apply, hc, sub_smul, mul_smul,
    ← Complex.coe_smul, ← Complex.coe_smul, smul_neg, ← sub_eq_add_neg]

/-- Riesz functional `x ↦ ⟪T x, y⟫` of an antilinear `T` (it is complex-linear in `x`). -/
def antiDual {T : F →L[ℝ] F} (hT : Antilinear T) (y : F) : F →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟪T x, y⟫_ℂ
      map_add' := fun x x' => by simp only [map_add, inner_add_left]
      map_smul' := fun a x => by
        simp only [anti_smul hT, inner_smul_left, Complex.conj_conj, RingHom.id_apply,
          smul_eq_mul] }
    (‖T‖ * ‖y‖) (fun x => by
      calc ‖⟪T x, y⟫_ℂ‖ ≤ ‖T x‖ * ‖y‖ := norm_inner_le_norm _ _
        _ ≤ ‖T‖ * ‖x‖ * ‖y‖ := mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg _)
        _ = ‖T‖ * ‖y‖ * ‖x‖ := by ring)

lemma antiDual_apply {T : F →L[ℝ] F} (hT : Antilinear T) (y x : F) :
    antiDual hT y x = ⟪T x, y⟫_ℂ := rfl

/-- The basis-free HS sum `∑ᵢ ‖T eᵢ‖²` of a real-linear map in a Hilbert basis `e`. -/
def antiHS {ι : Type*} (e : HilbertBasis ι ℂ F) (T : F →L[ℝ] F) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (‖T (e i)‖ ^ 2)

/-- Core identity: for any family `x` satisfying Parseval, `∑ᵢ ‖T xᵢ‖²` equals a quantity
depending only on `T` and a reference basis `c`. -/
theorem antiSum_eq_riesz [CompleteSpace F] {T : F →L[ℝ] F} (hT : Antilinear T)
    {κ ι : Type*} (c : HilbertBasis κ ℂ F) (x : ι → F)
    (hx : ∀ g : F, ∑' i, ENNReal.ofReal (‖⟪x i, g⟫_ℂ‖ ^ 2) = ENNReal.ofReal (‖g‖ ^ 2)) :
    ∑' i, ENNReal.ofReal (‖T (x i)‖ ^ 2) =
      ∑' j, ENNReal.ofReal (‖(InnerProductSpace.toDual ℂ F).symm (antiDual hT (c j))‖ ^ 2) := by
  calc ∑' i, ENNReal.ofReal (‖T (x i)‖ ^ 2)
      = ∑' i, ∑' j, ENNReal.ofReal (‖⟪c j, T (x i)⟫_ℂ‖ ^ 2) := by
        simp_rw [TraceClass.tsum_ofReal_norm_inner_sq]
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪c j, T (x i)⟫_ℂ‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ENNReal.ofReal
          (‖⟪x i, (InnerProductSpace.toDual ℂ F).symm (antiDual hT (c j))⟫_ℂ‖ ^ 2) := by
        congr 1; ext j; congr 1; ext i
        rw [norm_inner_symm (x i), InnerProductSpace.toDual_symm_apply, antiDual_apply,
          norm_inner_symm]
    _ = _ := by simp_rw [hx]

/-- **Basis independence** of the HS sum of an antilinear operator. -/
theorem antiHS_basis_indep [CompleteSpace F] {T : F →L[ℝ] F} (hT : Antilinear T)
    {ι κ : Type*} (e : HilbertBasis ι ℂ F) (e' : HilbertBasis κ ℂ F) :
    antiHS e T = antiHS e' T := by
  unfold antiHS
  rw [antiSum_eq_riesz hT e (fun i => e i) (fun g => TraceClass.tsum_ofReal_norm_inner_sq e g),
    antiSum_eq_riesz hT e (fun i => e' i) (fun g => TraceClass.tsum_ofReal_norm_inner_sq e' g)]

/-! ### Unitary transport of real-linear maps -/

/-- `U⁻¹ ∘ T ∘ U` as a bounded real-linear map. -/
def pull (U : H ≃ₗᵢ[ℂ] F) (T : F →L[ℝ] F) : H →L[ℝ] H :=
  (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) ∘L T ∘L
    (U.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)

@[simp] lemma pull_apply (U : H ≃ₗᵢ[ℂ] F) (T : F →L[ℝ] F) (x : H) :
    pull U T x = U.symm (T (U x)) := rfl

lemma pull_add (U : H ≃ₗᵢ[ℂ] F) (T T' : F →L[ℝ] F) : pull U (T + T') = pull U T + pull U T' := by
  ext x; simp

lemma norm_pull (U : H ≃ₗᵢ[ℂ] F) (T : F →L[ℝ] F) : ‖pull U T‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [pull_apply, LinearIsometryEquiv.norm_map]
    simpa only [LinearIsometryEquiv.norm_map] using T.le_opNorm (U x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    have h := (pull U T).le_opNorm (U.symm y)
    rw [pull_apply, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map,
      LinearIsometryEquiv.norm_map] at h
    exact h

lemma J_map (U : H ≃ₗᵢ[ℂ] F) (x : H) : U (J x) = J (U x) := by
  simp only [J_apply, map_smul]

lemma J_symm (U : H ≃ₗᵢ[ℂ] F) (y : F) : U.symm (J y) = J (U.symm y) := by
  simp only [J_apply, map_smul]

lemma real_smul_map (U : H ≃ₗᵢ[ℂ] F) (r : ℝ) (y : F) : U.symm (r • y) = r • U.symm y := by
  rw [← Complex.coe_smul, ← Complex.coe_smul, map_smul]

lemma complexPart_pull (U : H ≃ₗᵢ[ℂ] F) (T : F →L[ℝ] F) :
    complexPart (pull U T) = pull U (complexPart T) := by
  ext x
  simp only [complexPart_apply, pull_apply, J_map, real_smul_map, map_sub]

lemma antilinearPart_pull (U : H ≃ₗᵢ[ℂ] F) (T : F →L[ℝ] F) :
    antilinearPart (pull U T) = pull U (antilinearPart T) := by
  ext x
  simp only [antilinearPart_apply, pull_apply, J_map, real_smul_map, map_add]

lemma pull_antilinear (U : H ≃ₗᵢ[ℂ] F) {T : F →L[ℝ] F} (hT : Antilinear T) :
    Antilinear (pull U T) := by
  intro x
  rw [pull_apply, pull_apply, J_map, hT, map_neg, J_symm]

lemma pull_clinear (U : H ≃ₗᵢ[ℂ] F) {T : F →L[ℝ] F} (hT : CLinear T) :
    CLinear (pull U T) := by
  intro x
  rw [pull_apply, pull_apply, J_map, hT, J_symm]

lemma inner_pull (U : H ≃ₗᵢ[ℂ] F) (T : F →L[ℝ] F) (x y : H) :
    ⟪x, pull U T y⟫_ℂ = ⟪U x, T (U y)⟫_ℂ := by
  rw [pull_apply, ← LinearIsometryEquiv.inner_map_map U, LinearIsometryEquiv.apply_symm_apply]

/-- **Transport of the intrinsic HS sum**: computed in any basis of `H` for `U⁻¹TU` it equals
the sum for `T` in any basis of `F`. -/
theorem antiHS_pull [CompleteSpace F] (U : H ≃ₗᵢ[ℂ] F) {T : F →L[ℝ] F} (hT : Antilinear T)
    {ι κ : Type*} (e : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ F) :
    antiHS e (pull U T) = antiHS c T := by
  have hx : ∀ g : F, ∑' i, ENNReal.ofReal (‖⟪U (e i), g⟫_ℂ‖ ^ 2) = ENNReal.ofReal (‖g‖ ^ 2) := by
    intro g
    have h := TraceClass.tsum_ofReal_norm_inner_sq e (U.symm g)
    rw [LinearIsometryEquiv.norm_map] at h
    rw [← h]
    congr 1; ext i
    rw [LinearIsometryEquiv.inner_map_eq_flip]
  have hl : antiHS e (pull U T) = ∑' i, ENNReal.ofReal (‖T (U (e i))‖ ^ 2) := by
    unfold antiHS
    congr 1; ext i
    rw [pull_apply, LinearIsometryEquiv.norm_map]
  rw [hl, antiSum_eq_riesz hT c (fun i => U (e i)) hx]
  unfold antiHS
  rw [antiSum_eq_riesz hT c (fun i => c i) (fun g => TraceClass.tsum_ofReal_norm_inner_sq c g)]

/-! ### Parts of complex-linear and antilinear maps -/

lemma complexPart_of_clinear {T : F →L[ℝ] F} (hT : CLinear T) : complexPart T = T := by
  ext x
  rw [complexPart_apply, hT, J_sq]
  module

lemma antilinearPart_of_clinear {T : F →L[ℝ] F} (hT : CLinear T) : antilinearPart T = 0 := by
  ext x
  rw [antilinearPart_apply, hT, J_sq, ContinuousLinearMap.zero_apply]
  module

lemma complexPart_of_antilinear {T : F →L[ℝ] F} (hT : Antilinear T) : complexPart T = 0 := by
  ext x
  rw [complexPart_apply, hT, map_neg, J_sq, ContinuousLinearMap.zero_apply]
  module

lemma antilinearPart_of_antilinear {T : F →L[ℝ] F} (hT : Antilinear T) :
    antilinearPart T = T := by
  ext x
  rw [antilinearPart_apply, hT, map_neg, J_sq]
  module

lemma complexPart_clinear (T : F →L[ℝ] F) : CLinear (complexPart T) :=
  complexPart_commutes_J T

lemma antilinearPart_antilinear (T : F →L[ℝ] F) : Antilinear (antilinearPart T) :=
  antilinearPart_anticommutes_J T

/-- In a fixed basis the intrinsic sum is the frozen EXT-006 `hsSq b (beta b S)`. -/
theorem antiHS_eq_hsSq_beta [CompleteSpace F] {ι : Type*} (b : HilbertBasis ι ℂ F)
    (S : F ≃L[ℝ] F) :
    antiHS b (antilinearPart S.toContinuousLinearMap) =
      TraceClass.hsSq b (Ext006KernelHilbertSchmidt.beta b S) :=
  (Ext006KernelHilbertSchmidt.beta_hsSq_eq_intrinsic b S).symm

/-- A complex-linear operator in a fixed basis: `T ∘ C_b` is antilinear and its intrinsic sum is
`hsSq b T`. -/
theorem antiHS_comp_conjugation [CompleteSpace F] {ι : Type*} (b : HilbertBasis ι ℂ F)
    (T : F →L[ℂ] F) :
    antiHS b (T.restrictScalars ℝ ∘L Ext006KernelHilbertSchmidt.conjugation b) =
      TraceClass.hsSq b T := by
  unfold antiHS TraceClass.hsSq
  congr 1; ext i
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    Ext006KernelHilbertSchmidt.conjugation_basis]

lemma comp_conjugation_antilinear {ι : Type*} (b : HilbertBasis ι ℂ F) (T : F →L[ℂ] F) :
    Antilinear (T.restrictScalars ℝ ∘L Ext006KernelHilbertSchmidt.conjugation b) := by
  intro x
  show T (Ext006KernelHilbertSchmidt.conjugation b (J x)) =
    -J (T (Ext006KernelHilbertSchmidt.conjugation b x))
  rw [Ext006KernelHilbertSchmidt.conjugation_J, J_apply, J_apply, map_neg, map_smul]

lemma restrictScalars_clinear (T : F →L[ℂ] F) : CLinear (T.restrictScalars ℝ) := by
  intro x
  simp only [ContinuousLinearMap.coe_restrictScalars', J_apply, map_smul]

end QuantumNLS.Prop022GAntiHS

#print axioms QuantumNLS.Prop022GAntiHS.antiHS_basis_indep
#print axioms QuantumNLS.Prop022GAntiHS.antiHS_pull
#print axioms QuantumNLS.Prop022GAntiHS.norm_pull
#print axioms QuantumNLS.Prop022GAntiHS.antiHS_eq_hsSq_beta
#print axioms QuantumNLS.Prop022GAntiHS.antiHS_comp_conjugation
