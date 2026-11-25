import QuantumNLS.Ext005AntidualR113
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Completion

/-! Energy completion of the domain of a positive self-adjoint operator.
The Hilbert energy space and its injective dense inclusion are constructed
from A >= 1. Neither the form-domain embedding nor its injectivity is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory UniformSpace
namespace QuantumNLS.Ext005OperatorFormR113
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The literal abstract positive self-adjoint operator hypothesis A >= 1. -/
structure PositiveOperator (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  op : H →ₗ.[ℂ] H
  selfAdjoint : IsSelfAdjoint op
  lower : ∀ u : op.domain, ‖(u : H)‖ ^ 2 ≤ (⟪(u : H), op u⟫_ℂ).re

variable (S : PositiveOperator H)

lemma operator_symmetric : S.op.IsFormalAdjoint S.op := by
  have h := S.op.adjoint_isFormalAdjoint S.selfAdjoint.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp S.selfAdjoint] at h

/-- The operator domain endowed with the energy inner product. -/
def Core : Type _ := S.op.domain
instance : AddCommGroup (Core S) := inferInstanceAs (AddCommGroup S.op.domain)
instance : Module ℂ (Core S) := inferInstanceAs (Module ℂ S.op.domain)

def coreVal (u : Core S) : H := (show S.op.domain from u).val

@[instance_reducible] def coreEnergy : InnerProductSpace.Core ℂ (Core S) where
  inner u v := ⟪coreVal S u, S.op (show S.op.domain from v)⟫_ℂ
  conj_inner_symm u v := by
    rw [inner_conj_symm]
    exact operator_symmetric S u v
  re_inner_nonneg u := (sq_nonneg ‖coreVal S u‖).trans (S.lower u)
  add_left u v w := inner_add_left _ _ _
  smul_left u v c := inner_smul_left _ _ _
  definite u hu := by
    have h := S.lower u
    change ‖coreVal S u‖ ^ 2 ≤ (⟪coreVal S u, S.op u⟫_ℂ).re at h
    rw [hu, Complex.zero_re] at h
    have hn : ‖coreVal S u‖ = 0 := by nlinarith [norm_nonneg (coreVal S u)]
    exact Subtype.ext (norm_eq_zero.mp hn)

instance : NormedAddCommGroup (Core S) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (Core S) _ _ _ (coreEnergy S)
instance : InnerProductSpace ℂ (Core S) := InnerProductSpace.ofCore (coreEnergy S).toCore

lemma core_inner (u v : Core S) :
    ⟪u, v⟫_ℂ = ⟪coreVal S u, S.op (show S.op.domain from v)⟫_ℂ := rfl

lemma core_norm_sq (u : Core S) : ‖u‖ ^ 2 = (⟪coreVal S u, S.op u⟫_ℂ).re :=
  norm_sq_eq_re_inner (𝕜 := ℂ) u

lemma core_norm_domination (u : Core S) : ‖coreVal S u‖ ≤ ‖u‖ := by
  have h := S.lower u
  change ‖coreVal S u‖ ^ 2 ≤ (⟪coreVal S u, S.op u⟫_ℂ).re at h
  rw [← core_norm_sq S u] at h
  nlinarith [norm_nonneg (coreVal S u), norm_nonneg u]

def coreInclusion : Core S →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := coreVal S
      map_add' := by intro u v; rfl
      map_smul' := by intro c u; rfl }
    1 (by intro u; change ‖coreVal S u‖ ≤ 1 * ‖u‖; simpa using core_norm_domination S u)

/-- Q(A), as the completion of D(A) in its energy norm. -/
abbrev FormDomain := Completion (Core S)

/-- Canonical map Q(A) -> H, by continuous extension of D(A) -> H. -/
def inclusion : FormDomain S →L[ℂ] H :=
  (coreInclusion S).extend (Completion.toComplL : Core S →L[ℂ] FormDomain S)

@[simp] lemma inclusion_coe (u : Core S) : inclusion S (u : FormDomain S) = coreVal S u :=
  (coreInclusion S).extend_eq Completion.denseRange_coe (Completion.isUniformInducing_coe _) u

lemma inclusion_norm_le (u : FormDomain S) : ‖inclusion S u‖ ≤ ‖u‖ := by
  refine Completion.induction_on u (isClosed_le (by fun_prop) continuous_norm) ?_
  intro v
  simpa only [inclusion_coe, Completion.norm_coe] using core_norm_domination S v

/-- Symmetry identifies ambient tests against Av with the energy pairing. -/
lemma inclusion_pair (u : FormDomain S) (v : Core S) :
    ⟪inclusion S u, S.op (show S.op.domain from v)⟫_ℂ =
      ⟪u, (v : FormDomain S)⟫_ℂ := by
  refine Completion.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro w
  rw [inclusion_coe, Completion.inner_coe]
  rfl

lemma inclusion_zero (u : FormDomain S) (hu : inclusion S u = 0) : u = 0 := by
  have hz (v : FormDomain S) : ⟪u, v⟫_ℂ = 0 := by
    refine Completion.induction_on v (isClosed_eq (by fun_prop) continuous_const) ?_
    intro v
    rw [← inclusion_pair, hu, inner_zero_left]
  exact inner_self_eq_zero.mp (hz u)

/-- Closability, derived from symmetry, makes Q(A) an actual subspace of H. -/
lemma inclusion_injective : Function.Injective (inclusion S) := by
  intro u v h
  apply sub_eq_zero.mp
  apply inclusion_zero S (u - v)
  rw [map_sub, h, sub_self]

lemma inclusion_dense : DenseRange (inclusion S) := by
  apply S.selfAdjoint.dense_domain.mono
  intro x hx
  let u : Core S := ⟨x, hx⟩
  exact ⟨(u : FormDomain S), inclusion_coe S u⟩

end QuantumNLS.Ext005OperatorFormR113
#print axioms QuantumNLS.Ext005OperatorFormR113.inclusion_injective
#print axioms QuantumNLS.Ext005OperatorFormR113.inclusion_dense

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005OperatorFormR113." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005OperatorFormR113." then
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
  Lean.logInfo m!"R113 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
