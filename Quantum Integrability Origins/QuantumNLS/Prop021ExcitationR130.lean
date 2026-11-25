import QuantumNLS.GenericUAdjoint
import QuantumNLS.Ext025A12Tensor
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! Literal excitation operator and square-root contraction on every
symmetric sector, for an arbitrary complex Hilbert space. The placement
is the source reciprocal-binomial average, not a new observable premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 10000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace ComplexOrder
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.Prop021ExcitationR130
open TensorCarrier TensorPlacements KernelDefinition
section OperatorCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance (priority := 1500) opComplexAlgebra : NormedAlgebra ℂ (E →L[ℂ] E) :=
  ContinuousLinearMap.toNormedAlgebra
local instance (priority := 1500) opRealAlgebra : NormedAlgebra ℝ (E →L[ℂ] E) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

/-- Generic CFC root, before selecting a dependent symmetric tensor carrier. -/
def operatorRoot (T : E →L[ℂ] E) : E →L[ℂ] E := CFC.sqrt T

lemma operatorRoot_square (T : E →L[ℂ] E) (hT : T.IsPositive) :
    operatorRoot T * operatorRoot T = T :=
  CFC.sqrt_mul_sqrt_self T (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT)

lemma operatorRoot_adjoint (T : E →L[ℂ] E) : (operatorRoot T).adjoint = operatorRoot T :=
  (CFC.sqrt_nonneg T).isSelfAdjoint.adjoint_eq

lemma operatorRoot_norm (T : E →L[ℂ] E) (hT : T.IsPositive) :
    ‖operatorRoot T‖ = Real.sqrt ‖T‖ :=
  CFC.norm_sqrt T (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT)

lemma operatorRoot_positive (T : E →L[ℂ] E) : (operatorRoot T).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)

lemma operatorRoot_unique (T K : E →L[ℂ] E) (hT : T.IsPositive) (hK : K.IsPositive)
    (h : K*K=T) : operatorRoot T=K :=
  (CFC.sqrt_eq_iff T K (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT)
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr hK)).mpr h

lemma real_scale_positive (T : E →L[ℂ] E) (hT : T.IsPositive) (c : ℝ) (hc : 0 ≤ c) :
    ((c:ℂ) • T).IsPositive := hT.smul_of_nonneg (by exact_mod_cast hc)
end OperatorCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance (priority := 1200) sectorOpNormed (n : ℕ) :
    NormedAddCommGroup (SymSector ℂ H n →L[ℂ] SymSector ℂ H n) := inferInstance

/-- Positivity survives the actual extension, tensor amplification,
isometric split, symmetrization and restriction in DEF-009. -/
lemma positive_extend {r : ℕ} (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (hA : A.IsPositive) : (extendSymKernel A).IsPositive := by
  simpa only [extendSymKernel, BethePhysicalTransfer.symProjToSector_eq_adjoint,
    ContinuousLinearMap.comp_assoc] using hA.conj_adjoint (SymSector ℂ H r).subtypeL

lemma positive_first {r q : ℕ} (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (hA : A.IsPositive) : (firstPlacement (q := q) A).IsPositive := by
  have h := (Ext025A12Tensor.ampliate_positive (Y := HilbertTensorPower ℂ H q)
    (extendSymKernel A) (positive_extend A hA)).adjoint_conj
      (splitIsometry (𝕜 := ℂ) (E := H) r q).toLinearIsometry.toContinuousLinearMap
  rw [GenericUAdjoint.adjoint_iso] at h
  simpa only [TensorCarrier.ampliate_apply,firstPlacement,ContinuousLinearMap.comp_assoc] using h

lemma positive_U {r q : ℕ} (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (hA : A.IsPositive) : (U_N_r (q := q) A).IsPositive := by
  have h := (positive_first (q := q) A hA).orthogonalProjectionOnto_comp
    (SymSector ℂ H (r+q))
  have he : U_N_r (q := q) A =
      (SymSector ℂ H (r+q)).orthogonalProjectionOnto ∘L firstPlacement (q := q) A ∘L
        (SymSector ℂ H (r+q)).subtypeL := by
    rw [U_N_r_eq_sandwich]
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change symProj ℂ H (r+q) (firstPlacement A (symProj ℂ H (r+q) x.val)) = _
    rw [symProj_eq_starProjection, Submodule.starProjection_eq_self_iff.mpr x.property]
    rfl
  rwa [he]

lemma positive_cast {n m : ℕ} (h : n=m) (A : SymSector ℂ H n →L[ℂ] SymSector ℂ H n)
    (hA : A.IsPositive) : (castSymSectorOperator h A).IsPositive := by
  subst m
  exact hA

lemma positive_generic (N r : ℕ) (hr : r ≤ N)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) (hA : A.IsPositive) :
    (genericU_N_r N r hr A).IsPositive :=
  positive_cast _ _ (positive_U A hA)

def condensate (u : H) : SymSector ℂ H 1 := ⟨htpow 1 u, htpow_mem_symSector 1 u⟩

lemma condensate_norm (u : H) : ‖condensate u‖ = ‖u‖ := by
  change ‖(htpow 1 u : HilbertTensorPower ℂ H 1)‖ = _
  rw [norm_htpow, pow_one]

/-- Literal one-particle complementary condensate projection. -/
def q (u : H) : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1 :=
  1 - InnerProductSpace.rankOne ℂ (condensate u) (condensate u)

lemma q_projection (u : H) (hu : ‖u‖=1) : IsStarProjection (q u) :=
  (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ)
    ((condensate_norm u).trans hu)).one_sub

lemma q_positive (u : H) (hu : ‖u‖=1) : (q u).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (q_projection u hu).nonneg

lemma q_norm (u : H) (hu : ‖u‖=1) : ‖q u‖ ≤ 1 :=
  IsStarProjection.norm_le (q u) (q_projection u hu)

lemma q_condensate (u : H) (hu : ‖u‖=1) : q u (condensate u) = 0 := by
  simp only [q, sub_apply, one_apply_eq_self,
    InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, condensate_norm, hu]
  simp

/-- The average of q in the N tensor slots; zero on the vacuum. -/
def average (u : H) (N : ℕ) : SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  if h : 1 ≤ N then genericU_N_r N 1 h (q u) else 0

lemma average_positive (u : H) (hu : ‖u‖=1) (N : ℕ) : (average u N).IsPositive := by
  unfold average
  split_ifs with h
  · exact positive_generic N 1 h (q u) (q_positive u hu)
  · exact ContinuousLinearMap.isPositive_zero

lemma average_norm (u : H) (hu : ‖u‖=1) (N : ℕ) : ‖average u N‖ ≤ 1 := by
  unfold average
  split_ifs with h
  · exact (norm_genericU_N_r_le N 1 h (q u)).trans (q_norm u hu)
  · simp only [ContinuousLinearMap.opNorm_zero,zero_le_one]

/-- dGamma(q) on the actual N-particle sector. -/
def excitation (u : H) (N : ℕ) : SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  (N : ℂ) • average u N

/-- The nonnegative functional-calculus square root of D_N/N. -/
def contraction (u : H) (N : ℕ) : SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  operatorRoot (average u N)

lemma contraction_sq (u : H) (hu : ‖u‖=1) (N : ℕ) :
    contraction u N * contraction u N = average u N :=
  operatorRoot_square _ (average_positive u hu N)

lemma contraction_adjoint (u : H) (N : ℕ) : (contraction u N).adjoint = contraction u N :=
  operatorRoot_adjoint (average u N)

/-- The literal excitation square root is a contraction, proved from the
actual projection and average placement; no contraction premise is supplied. -/
theorem contraction_norm (u : H) (hu : ‖u‖=1) (N : ℕ) : ‖contraction u N‖ ≤ 1 := by
  rw [contraction, operatorRoot_norm _ (average_positive u hu N)]
  exact (Real.sqrt_le_sqrt (average_norm u hu N)).trans_eq Real.sqrt_one

/-- Exact quadratic-form identity used in the marginal depletion step. -/
theorem contraction_expectation (u : H) (hu : ‖u‖=1) (N : ℕ)
    (x : SymSector ℂ H N) :
    ‖contraction u N x‖^2 = (⟪x,average u N x⟫_ℂ).re := by
  rw [(contraction u N).apply_norm_sq_eq_inner_adjoint_right x, contraction_adjoint]
  change (⟪x,(contraction u N * contraction u N) x⟫_ℂ).re = _
  rw [contraction_sq u hu]

/-- Square root of D_N, before normalization by the fixed particle count. -/
def excitationRoot (u : H) (N : ℕ) : SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  (Real.sqrt (N:ℝ) : ℂ) • contraction u N

lemma excitationRoot_sq (u : H) (hu : ‖u‖=1) (N : ℕ) :
    excitationRoot u N * excitationRoot u N = excitation u N := by
  apply ContinuousLinearMap.ext
  intro x
  have hh := congrArg (fun T : SymSector ℂ H N →L[ℂ] SymSector ℂ H N => T x)
    (contraction_sq u hu N)
  change contraction u N (contraction u N x)=average u N x at hh
  simp only [excitationRoot,excitation,mul_apply_eq_comp,smul_apply,map_smul,smul_smul]
  rw [hh,← Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg N)]
  rfl

lemma excitation_positive (u : H) (hu : ‖u‖=1) (N : ℕ) : (excitation u N).IsPositive :=
  real_scale_positive _ (average_positive u hu N) (N:ℝ) (Nat.cast_nonneg N)

lemma excitationRoot_positive (u : H) (N : ℕ) : (excitationRoot u N).IsPositive :=
  real_scale_positive _ (operatorRoot_positive (average u N)) (Real.sqrt (N:ℝ)) (Real.sqrt_nonneg _)

/-- Identify the constructed root with the UNIQUE nonnegative CFC square
root of the literal sector dGamma(q); this fixes its physical meaning. -/
theorem excitationRoot_eq_sqrt (u : H) (hu : ‖u‖=1) (N : ℕ) :
    excitationRoot u N = operatorRoot (excitation u N) :=
  (operatorRoot_unique _ _ (excitation_positive u hu N) (excitationRoot_positive u N)
    (excitationRoot_sq u hu N)).symm

/-- Domination D_N <= N in the exact squared-vector form. -/
theorem excitationRoot_bound (u : H) (hu : ‖u‖=1) (N : ℕ)
    (x : SymSector ℂ H N) : ‖excitationRoot u N x‖^2 ≤ (N:ℝ)*‖x‖^2 := by
  have hb : ‖contraction u N x‖ ≤ ‖x‖ :=
    (ContinuousLinearMap.le_opNorm _ x).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (contraction_norm u hu N) (norm_nonneg x))
  simp only [excitationRoot, smul_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (Nat.cast_nonneg N)

end QuantumNLS.Prop021ExcitationR130
#print axioms QuantumNLS.Prop021ExcitationR130.positive_generic
#print axioms QuantumNLS.Prop021ExcitationR130.contraction_norm
#print axioms QuantumNLS.Prop021ExcitationR130.contraction_expectation
#print axioms QuantumNLS.Prop021ExcitationR130.excitationRoot_sq
#print axioms QuantumNLS.Prop021ExcitationR130.excitationRoot_bound
#print axioms QuantumNLS.Prop021ExcitationR130.excitationRoot_eq_sqrt

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021ExcitationR130"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R130 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
