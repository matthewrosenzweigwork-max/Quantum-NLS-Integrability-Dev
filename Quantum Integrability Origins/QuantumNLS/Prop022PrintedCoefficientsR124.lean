import QuantumNLS.Prop022SymplecticR123
import QuantumNLS.Prop022PairHSR122

/-! Identification of the real variational equation with the literal physical
number and pair coefficients of Q7B:eq:linearized. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace ComplexConjugate Topology
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.Prop022PrintedCoefficientsR124
open TensorCarrier TensorFourier PhysicalTensor BetheCoefficientTransform
open Prop022TensorCompressionR115 Prop022FactorialCoefficientsR115
open Prop022HessianR118 Prop022VariationalR123 Prop022SymplecticR123
open Prop022PairHSR122 Ext006PairDensityR40a Ext006PhysicalNormBridge.PairTensor
open Ext006KernelHilbertSchmidt Prop022ActualProfileR117
variable {L : ℝ} [Fact (0 < L)]
local instance : Inner ℝ (L2T L) := Inner.rclikeToReal ℂ (L2T L)
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup

/-- The canonical first symmetric tensor embedding on the original carrier. -/
def oneEmbedding : L2T L →L[ℂ] HN L 1 :=
  (physSector L 1).orthogonalProjectionOnto ∘L
    (firstPowerIso (𝕜 := ℂ) (E := L2T L)).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma oneEmbedding_apply (x : L2T L) : oneEmbedding x = power 1 x := by
  have he : (firstPowerIso (𝕜 := ℂ) (E := L2T L)).symm x = htpow 1 x := by
    apply (firstPowerIso (𝕜 := ℂ) (E := L2T L)).injective
    rw [LinearIsometryEquiv.apply_symm_apply, firstPowerIso_htpow]
  change (physSector L 1).orthogonalProjectionOnto
    ((firstPowerIso (𝕜 := ℂ) (E := L2T L)).symm x) = _
  rw [he]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (power 1 x)

lemma oneEmbedding_norm_le : ‖oneEmbedding (L := L)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  rw [oneEmbedding_apply, power_norm, pow_one, one_mul]

/-- The literal number coefficient transported through the canonical first
symmetric tensor embedding, without changing the complex structure. -/
def numberOperator (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) : L2T L →L[ℂ] L2T L :=
  oneEmbedding.adjoint ∘L numberCoefficient B u ∘L oneEmbedding

lemma numberOperator_pairing (B : ∀ m, HN L m →L[ℂ] HN L m) (u x y : L2T L) :
    ⟪x, numberOperator B u y⟫_ℂ =
      ⟪power 1 x, numberCoefficient B u (power 1 y)⟫_ℂ := by
  simp only [numberOperator, comp_apply, adjoint_inner_right, oneEmbedding_apply]

lemma numberOperator_adjoint (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (u : L2T L) :
    (numberOperator B u).adjoint = numberOperator B u := by
  simp only [numberOperator, adjoint_comp, adjoint_adjoint,
    numberCoefficient_adjoint B hs u, comp_assoc]

lemma numberOperator_norm_le (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) :
    ‖numberOperator B u‖ ≤ ‖numberCoefficient B u‖ := by
  calc
    _ ≤ ‖(oneEmbedding (L := L)).adjoint‖ *
        (‖numberCoefficient B u‖ * ‖oneEmbedding (L := L)‖) :=
      (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
        (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖numberCoefficient B u‖ * 1) := by
      rw [adjoint.norm_map]
      gcongr <;> exact oneEmbedding_norm_le
    _ = _ := by ring

lemma pairKernel_conjugation (B : ∀ m, HN L m →L[ℂ] HN L m) (u x : L2T L) :
    pairKernel B u (conjugation (physicalBasis L) x) =
      contract x (twoIso (pairCoefficient B u : HilbertTensorPower ℂ (L2T L) 2)) := by
  change contract (conjugation _ (conjugation _ x)) _ = _
  rw [conjugation_sq]

lemma pairTensor_flip (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) :
    htcommIsometry ℂ (L2T L) (L2T L)
      (twoIso (pairCoefficient B u : HilbertTensorPower ℂ (L2T L) 2)) =
      twoIso (pairCoefficient B u : HilbertTensorPower ℂ (L2T L) 2) := by
  rw [← twoIso_swap]
  exact congrArg twoIso ((pairCoefficient B u).property (Equiv.swap (0 : Fin 2) 1))

lemma pairKernel_pairing_symmetric (B : ∀ m, HN L m →L[ℂ] HN L m)
    (u x y : L2T L) :
    ⟪x, pairKernel B u (conjugation (physicalBasis L) y)⟫_ℂ =
      ⟪y, pairKernel B u (conjugation (physicalBasis L) x)⟫_ℂ := by
  rw [pairKernel_conjugation, pairKernel_conjugation, inner_contract, inner_contract]
  have h := (htcommIsometry ℂ (L2T L) (L2T L)).inner_map_map
    (htmul y x) (twoIso (pairCoefficient B u : HilbertTensorPower ℂ (L2T L) 2))
  rw [htcommIsometry_htmul, pairTensor_flip] at h
  exact h.symm

lemma pairKernel_pairing_diagonal (B : ∀ m, HN L m →L[ℂ] HN L m) (u x : L2T L) :
    ⟪x, pairKernel B u (conjugation (physicalBasis L) x)⟫_ℂ =
      ⟪power 2 x, pairCoefficient B u⟫_ℂ := by
  rw [pairKernel_conjugation, inner_contract]
  have h := (twoIso (E := L2T L)).inner_map_map
    (power 2 x : HilbertTensorPower ℂ (L2T L) 2)
    (pairCoefficient B u : HilbertTensorPower ℂ (L2T L) 2)
  rw [show twoIso (power 2 x : HilbertTensorPower ℂ (L2T L) 2) = htmul x x from
    twoIso_ptprod (fun _ => x)] at h
  exact h

/-- The two literal physical blocks, viewed as a real map. -/
def coefficientMap (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) : L2T L →L[ℝ] L2T L :=
  (numberOperator B u).restrictScalars ℝ +
    (pairKernel B u).restrictScalars ℝ ∘L conjugation (physicalBasis L)

lemma coefficientMap_symmetric (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (u x y : L2T L) :
    (⟪x, coefficientMap B u y⟫_ℂ).re = (⟪y, coefficientMap B u x⟫_ℂ).re := by
  have ha : (⟪x, numberOperator B u y⟫_ℂ).re =
      (⟪y, numberOperator B u x⟫_ℂ).re := by
    rw [← adjoint_inner_left, numberOperator_adjoint B hs u]
    exact inner_re_symm (𝕜 := ℂ) _ _
  change (⟪x, numberOperator B u y + pairKernel B u (conjugation _ y)⟫_ℂ).re =
    (⟪y, numberOperator B u x + pairKernel B u (conjugation _ x)⟫_ℂ).re
  simp only [inner_add_right, Complex.add_re]
  rw [ha, pairKernel_pairing_symmetric B u x y]

lemma coefficientMap_diagonal (B : ∀ m, HN L m →L[ℂ] HN L m) (u x : L2T L) :
    coefficientDiagonal B u x = 2 * (⟪x, coefficientMap B u x⟫_ℂ).re := by
  change _ = 2 * (⟪x, numberOperator B u x + pairKernel B u (conjugation _ x)⟫_ℂ).re
  rw [inner_add_right, Complex.add_re, numberOperator_pairing, pairKernel_pairing_diagonal]
  unfold coefficientDiagonal
  ring

/-- The Hessian/Riesz derivative is exactly a v + b conjugate(v). This is a
conclusion of the factorial series, tensor symmetry, and real polarization. -/
theorem gradientDerivative_eq_coefficients (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) :
    gradientDerivative B u = coefficientMap B u := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  change (⟪gradientDerivative B u x, y⟫_ℂ).re = (⟪coefficientMap B u x, y⟫_ℂ).re
  rw [gradientDerivative_pairing]
  have h := seriesHessian_eq_coefficients B hs M A hA hB u x y hu
  simp_rw [coefficientMap_diagonal] at h
  simp only [map_add, inner_add_left, inner_add_right, Complex.add_re] at h
  have hs' := coefficientMap_symmetric B hs u x y
  have hr := inner_re_symm (𝕜 := ℂ) (coefficientMap B u x) y
  change (⟪coefficientMap B u x, y⟫_ℂ).re = (⟪y, coefficientMap B u x⟫_ℂ).re at hr
  linarith

/-- The printed equation i vdot = a_t v + b_t conjugate(v), with the actual
source coefficients and the constructed variational evolution, at all signed times. -/
theorem flow_printed_linearized (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L))
    (s t : ℝ) (x : L2T L) :
    Complex.I • deriv (fun r => flow B M A hA hB hs u₀ r s x) t =
      numberOperator B (profile B M A hA hB hs u₀ t) (flow B M A hA hB hs u₀ t s x) +
      pairKernel B (profile B M A hA hB hs u₀ t)
        (conjugation (physicalBasis L) (flow B M A hA hB hs u₀ t s x)) := by
  rw [(flow_variational B M A hA hB hs u₀ s t x).deriv,
    (velocity_hasFDerivAt B hs M A hA hB _).fderiv]
  change Complex.I • ((-Complex.I) • gradientDerivative B _ _) = _
  rw [gradientDerivative_eq_coefficients B hs M A hA hB _
    ((profile_spec B M A hA hB hs u₀).2.2.1 t), smul_smul]
  simp only [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  rfl

end QuantumNLS.Prop022PrintedCoefficientsR124
#print axioms QuantumNLS.Prop022PrintedCoefficientsR124.gradientDerivative_eq_coefficients
#print axioms QuantumNLS.Prop022PrintedCoefficientsR124.flow_printed_linearized

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022PrintedCoefficientsR124." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022PrintedCoefficientsR124." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R124 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
