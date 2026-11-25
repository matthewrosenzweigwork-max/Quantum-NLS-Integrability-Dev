import Mathlib
import QuantumNLS.Prop022BFock3

/-! PROP-022 route A, finite-dimensional case, stage B4c: the classical coefficients `a_t, b_t` (complex-linear
resp. antilinear operators on `H`, parts of the Hessian `D(∇F)(u_t)`) and their Fock-sector representatives
`aSymJ t ∈ B(Sym¹H)`, `bSymJ t ∈ Sym²H` are the same data:

* `aSymJ_rep`:  `⟪x^{⊗1}, aSymJ t (y^{⊗1})⟫ = ⟪x, a_t y⟫`  (all `x, y ∈ H`);
* `bSymJ_rep`:  `⟪x, b_t y⟫ = ⟪htmul y x, twoIso (bSymJ t)⟫`  (`b_t` is the antilinear operator whose pairing
  with `x` is the Hilbert tensor `y ⊗ x` against the pair vector `bSymJ t ∈ Sym²H`).

Both are intrinsic on `H`; the frozen torus statement `bH'_pair` (`⟪w, b'_t z⟫ = ⟪htmul z w, twoIso (pairCoefficient)⟫`)
and the compatibility `inner_twoIso_tensorMapI` of the Hilbert tensor with `J^{⊗2}` are proved here. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022BCoef
open TensorCarrier PhysicalTensor Prop022GTensor Prop022AIsoTensor Prop022GClassical Prop022GLinear
open Prop022BIso Prop022BClass1 Prop022BClass2 Prop022BFock2 Prop022BFock3
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022PositiveDataR126
open Prop022PrintedCoefficientsR124 Prop022PairHSR122 Ext006PairDensityR40a Ext006KernelHilbertSchmidt
open Ext006PhysicalNormBridge.PairTensor

section Tensor
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem inner_twoIso_tensorMapI (J : E →ₗᵢ[ℂ] F) (x y : E) (z : HilbertTensorPower ℂ E 2) :
    ⟪htmul (J y) (J x), twoIso (E := F) (tensorMapI J 2 z)⟫_ℂ =
      ⟪htmul y x, twoIso (E := E) z⟫_ℂ := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_const.inner ((twoIso (E := F)).continuous.comp
      (tensorMapI J 2).continuous)) (continuous_const.inner (twoIso (E := E)).continuous)
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      rw [tensorMapI_coe, map_smul, algMapI_ptprod, UniformSpace.Completion.coe_smul,
        UniformSpace.Completion.coe_smul, map_smul, map_smul, twoIso_ptprod, twoIso_ptprod,
        inner_smul_right, inner_smul_right, inner_htmul, inner_htmul]
      simp only [LinearIsometry.inner_map_map]
    | add x y hx hy =>
      rw [UniformSpace.Completion.coe_add, map_add, map_add, map_add, inner_add_right, inner_add_right,
        hx, hy]

end Tensor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

section Data
variable (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
  (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)
include hM

local notation "Bp" => BL (UI L) (kernelsI J K)
local notation "up" t => profile (BL (UI L) (kernelsI J K)) M A hA.le
  (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
  (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs)) (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) t

theorem bH'_pair (t : ℝ) (w z : L2T L) :
    ⟪w, bH (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀)
      (hJu J u₀ hu₀) t z⟫_ℂ =
      ⟪htmul z w, twoIso (E := L2T L)
        (pairCoefficient Bp (up t) : HilbertTensorPower ℂ (L2T L) 2)⟫_ℂ := by
  rw [bH_eq]
  change ⟪w, contract (conjugation (physicalBasis L) (conjugation (physicalBasis L) z))
    (twoIso (E := L2T L) (pairCoefficient Bp (up t) : HilbertTensorPower ℂ (L2T L) 2))⟫_ℂ = _
  rw [conjugation_sq, inner_contract]

/-- `a_t` and its Fock-sector representative `aSymJ t ∈ B(Sym¹ H)` agree on one-particle vectors. -/
theorem aSymJ_rep (t : ℝ) (x y : H) :
    ⟪powerH 1 x, aSymJ J K M A hA hK hs u₀ hu₀ t (powerH 1 y)⟫_ℂ =
      ⟪x, aJ J K M A hA.le hK hs u₀ hu₀ t y⟫_ℂ := by
  unfold aSymJ
  change ⟪powerH 1 x, symAdj J 1 (numberCoefficient Bp (up t) (symI J 1 (powerH 1 y)))⟫_ℂ = _
  rw [inner_symAdj_right, symI_power, symI_power]
  have h := (numberOperator_pairing Bp (up t) (J x) (J y)).symm
  change ⟪powerH 1 (J x), numberCoefficient Bp (up t) (powerH 1 (J y))⟫_ℂ = _ at h
  rw [h, numberOperator_eq J K M A hM hA hK hs u₀ hu₀ t (J y), Jadj_J,
    LinearIsometry.inner_map_map]

/-- `b_t` and its Fock-sector representative `bSymJ t ∈ Sym² H`: `⟪x, b_t y⟫ = ⟪y ⊗ x, bSymJ t⟫`. -/
theorem bSymJ_rep (t : ℝ) (x y : H) :
    ⟪x, bJ J K M A hA.le hK hs u₀ hu₀ t y⟫_ℂ =
      ⟪htmul y x, twoIso (E := H)
        (bSymJ J K M A hA hK hs u₀ hu₀ t : HilbertTensorPower ℂ H 2)⟫_ℂ := by
  rw [bJ_eq J K M A hA.le hK hs u₀ hu₀ t]
  simp only [ContinuousLinearMap.comp_apply, Jr_apply, Jar_apply]
  rw [inner_Jadj_right, bH'_pair J K M A hM hA hK hs u₀ hu₀ t]
  have h : (pairCoefficient Bp (up t) : HilbertTensorPower ℂ (L2T L) 2) =
      tensorMapI J 2 (bSymJ J K M A hA hK hs u₀ hu₀ t : HilbertTensorPower ℂ H 2) :=
    congrArg Subtype.val (symI_bSymJ J K M A hM hA hK hs u₀ hu₀ t).symm
  rw [h, inner_twoIso_tensorMapI]

end Data

end QuantumNLS.Prop022BCoef

#print axioms QuantumNLS.Prop022BCoef.aSymJ_rep
#print axioms QuantumNLS.Prop022BCoef.bSymJ_rep
