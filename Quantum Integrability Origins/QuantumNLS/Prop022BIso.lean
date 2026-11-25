import Mathlib
import QuantumNLS.Prop022GTensor
import QuantumNLS.Prop022AIsoTensor
import QuantumNLS.Prop022GClassical

/-! PROP-022 route A, finite-dimensional case, stage B2a: adjoint calculus of an isometric
embedding `J : E →ₗᵢ[ℂ] F`.

* `Jadj J = J*`, with `J* J = 1`;
* `inner_htpow_tensorMapI`: `⟪w^{⊗n}, J^{⊗n} z⟫ = ⟪(J* w)^{⊗n}, z⟫`;
* `symI J n = Γ_n(J)` and `symAdj J n = Γ_n(J)*` on the symmetric sectors, with
  `Γ_n(J)* (w^{⊗n}) = (J* w)^{⊗n}`;
* `kernelsI J K`: the kernels `Γ_{n+1}(J) K_n Γ_{n+1}(J)*` on `F`, same bound and self-adjointness,
  and the symbol identity `F_{kernelsI}(w) = F_K(J* w)`;
* `gamAdj J = Γ(J)*` on the Fock spaces (the Hilbert adjoint of `fockMapI J`), with the sector
  formula `(Γ(J)* y)_n = Γ_n(J)* y_n`, `Γ(J)* Γ(J) = 1`;
* `rot J z`: for `‖z‖ = 1` the unitary `Q + z (1 - Q)` of `F` (`Q = J J*`), fixing `range J`. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace

namespace QuantumNLS.Prop022BIso
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022AIsoTensor
open QuantumNLS.Prop022GClassical

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The Hilbert adjoint `J*` of a linear isometry. -/
def Jadj (J : E →ₗᵢ[ℂ] F) : F →L[ℂ] E := ContinuousLinearMap.adjoint J.toContinuousLinearMap

lemma inner_Jadj_left (J : E →ₗᵢ[ℂ] F) (y : F) (x : E) : ⟪Jadj J y, x⟫_ℂ = ⟪y, J x⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_left J.toContinuousLinearMap x y

lemma inner_Jadj_right (J : E →ₗᵢ[ℂ] F) (x : E) (y : F) : ⟪x, Jadj J y⟫_ℂ = ⟪J x, y⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right J.toContinuousLinearMap x y

lemma Jadj_J (J : E →ₗᵢ[ℂ] F) (x : E) : Jadj J (J x) = x := by
  apply ext_inner_right ℂ
  intro v
  rw [inner_Jadj_left, LinearIsometry.inner_map_map]

lemma norm_Jadj_le (J : E →ₗᵢ[ℂ] F) (y : F) : ‖Jadj J y‖ ≤ ‖y‖ := by
  have h := ContinuousLinearMap.le_opNorm (Jadj J) y
  have h1 : ‖Jadj J‖ ≤ 1 := by
    rw [Jadj, LinearIsometryEquiv.norm_map]
    exact LinearIsometry.norm_toContinuousLinearMap_le J
  nlinarith [norm_nonneg y, norm_nonneg (Jadj J y)]

/-! ### Tensor powers -/

theorem inner_htpow_tensorMapI (J : E →ₗᵢ[ℂ] F) (n : ℕ) (w : F) (z : HilbertTensorPower ℂ E n) :
    ⟪(htpow n w : HilbertTensorPower ℂ F n), tensorMapI J n z⟫_ℂ =
      ⟪(htpow n (Jadj J w) : HilbertTensorPower ℂ E n), z⟫_ℂ := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_const.inner (tensorMapI J n).continuous)
      (continuous_const.inner continuous_id)
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      rw [tensorMapI_coe, map_smul, algMapI_ptprod, UniformSpace.Completion.coe_smul,
        UniformSpace.Completion.coe_smul, htpow, htpow, inner_smul_right, inner_smul_right,
        UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe, inner_ptprod,
        inner_ptprod]
      congr 1
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [inner_Jadj_left]
    | add x y hx hy =>
      rw [UniformSpace.Completion.coe_add, map_add, inner_add_right, inner_add_right, hx, hy]

/-- `Γ_n(J)` on the symmetric sectors as a continuous linear map. -/
def symI (J : E →ₗᵢ[ℂ] F) (n : ℕ) : SymSector ℂ E n →L[ℂ] SymSector ℂ F n :=
  (symMapI J n).toContinuousLinearMap

/-- `Γ_n(J)*`. -/
def symAdj (J : E →ₗᵢ[ℂ] F) (n : ℕ) : SymSector ℂ F n →L[ℂ] SymSector ℂ E n :=
  ContinuousLinearMap.adjoint (symI J n)

@[simp] lemma symI_apply (J : E →ₗᵢ[ℂ] F) (n : ℕ) (x : SymSector ℂ E n) :
    symI J n x = symMapI J n x := rfl

lemma inner_symI (J : E →ₗᵢ[ℂ] F) (n : ℕ) (x y : SymSector ℂ E n) :
    ⟪symI J n x, symI J n y⟫_ℂ = ⟪x, y⟫_ℂ := (symMapI J n).inner_map_map x y

lemma inner_symAdj_left (J : E →ₗᵢ[ℂ] F) (n : ℕ) (y : SymSector ℂ F n) (x : SymSector ℂ E n) :
    ⟪symAdj J n y, x⟫_ℂ = ⟪y, symI J n x⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_left (symI J n) x y

lemma inner_symAdj_right (J : E →ₗᵢ[ℂ] F) (n : ℕ) (x : SymSector ℂ E n) (y : SymSector ℂ F n) :
    ⟪x, symAdj J n y⟫_ℂ = ⟪symI J n x, y⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right (symI J n) x y

lemma symAdj_symI (J : E →ₗᵢ[ℂ] F) (n : ℕ) (x : SymSector ℂ E n) :
    symAdj J n (symI J n x) = x := by
  apply ext_inner_right ℂ
  intro v
  rw [inner_symAdj_left, inner_symI]

lemma norm_symAdj_le (J : E →ₗᵢ[ℂ] F) (n : ℕ) (y : SymSector ℂ F n) :
    ‖symAdj J n y‖ ≤ ‖y‖ := by
  have h := ContinuousLinearMap.le_opNorm (symAdj J n) y
  have h1 : ‖symAdj J n‖ ≤ 1 := by
    rw [symAdj, LinearIsometryEquiv.norm_map]
    exact LinearIsometry.norm_toContinuousLinearMap_le (symMapI J n)
  nlinarith [norm_nonneg y, norm_nonneg (symAdj J n y)]

lemma norm_symI_le (J : E →ₗᵢ[ℂ] F) (n : ℕ) : ‖symI J n‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le (symMapI J n)

theorem symI_power (J : E →ₗᵢ[ℂ] F) (n : ℕ) (x : E) :
    symI J n (powerH n x) = powerH n (J x) :=
  Subtype.ext (tensorMapI_htpow J n x)

theorem symAdj_power (J : E →ₗᵢ[ℂ] F) (n : ℕ) (w : F) :
    symAdj J n (powerH n w) = powerH n (Jadj J w) := by
  apply ext_inner_right ℂ
  intro v
  rw [inner_symAdj_left]
  change ⟪(htpow n w : HilbertTensorPower ℂ F n), tensorMapI J n (v : HilbertTensorPower ℂ E n)⟫_ℂ =
    ⟪(htpow n (Jadj J w) : HilbertTensorPower ℂ E n), (v : HilbertTensorPower ℂ E n)⟫_ℂ
  exact inner_htpow_tensorMapI J n w v

/-! ### The compressed kernels -/

/-- `Γ_{n+1}(J) K_n Γ_{n+1}(J)*`. -/
def kernelsI (J : E →ₗᵢ[ℂ] F) (K : Kernels E) : Kernels F :=
  fun n => symI J (n + 1) ∘L K n ∘L symAdj J (n + 1)

lemma kernelsI_apply (J : E →ₗᵢ[ℂ] F) (K : Kernels E) (n : ℕ) (y : SymSector ℂ F (n + 1)) :
    kernelsI J K n y = symI J (n + 1) (K n (symAdj J (n + 1) y)) := rfl

lemma norm_kernelsI_le (J : E →ₗᵢ[ℂ] F) (K : Kernels E) (n : ℕ) :
    ‖kernelsI J K n‖ ≤ ‖K n‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) (fun y => ?_)
  rw [kernelsI_apply]
  calc ‖symI J (n + 1) (K n (symAdj J (n + 1) y))‖
      = ‖K n (symAdj J (n + 1) y)‖ := (symMapI J (n + 1)).norm_map _
    _ ≤ ‖K n‖ * ‖symAdj J (n + 1) y‖ := (K n).le_opNorm _
    _ ≤ ‖K n‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_left (norm_symAdj_le J (n + 1) y) (ContinuousLinearMap.opNorm_nonneg _)

lemma KBound_kernelsI (J : E →ₗᵢ[ℂ] F) (K : Kernels E) (M A : ℝ) (hK : KBound K M A) :
    KBound (kernelsI J K) M A :=
  fun n => (norm_kernelsI_le J K n).trans (hK n)

lemma KSelfAdj_kernelsI (J : E →ₗᵢ[ℂ] F) (K : Kernels E) (hs : KSelfAdj K) :
    KSelfAdj (kernelsI J K) := by
  intro n
  unfold kernelsI
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc]
  have h1 : (symAdj J (n + 1)).adjoint = symI J (n + 1) := by
    rw [symAdj, ContinuousLinearMap.adjoint_adjoint]
  have h2 : (symI J (n + 1)).adjoint = symAdj J (n + 1) := rfl
  rw [h1, h2, hs n]

/-- The symbol of the compressed kernels is the symbol of `K` composed with `J*`. -/
theorem symbolH_kernelsI (J : E →ₗᵢ[ℂ] F) (K : Kernels E) (w : F) :
    symbolH (kernelsI J K) w = symbolH K (Jadj J w) := by
  unfold symbolH
  congr 1
  funext n
  rw [kernelsI_apply, ← inner_symAdj_left, symAdj_power]

end QuantumNLS.Prop022BIso
