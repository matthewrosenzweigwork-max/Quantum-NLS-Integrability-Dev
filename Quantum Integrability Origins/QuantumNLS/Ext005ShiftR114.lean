import QuantumNLS.Ext005OperatorFormR113

/-! Real shifts of actual self-adjoint partial operators. This lets the
nonnegative comparison operator B use the constructed Q(B+1) completion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005ShiftR114
open Ext005OperatorFormR113
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def shift (T : H →ₗ.[ℂ] H) (c : ℝ) : H →ₗ.[ℂ] H where
  domain := T.domain
  toFun := T.toFun + (c : ℂ) • T.domain.subtype

omit [CompleteSpace H] in
@[simp] lemma shift_apply (T : H →ₗ.[ℂ] H) (c : ℝ) (u : T.domain) :
    shift T c u = T u + (c : ℂ) • (u : H) := rfl

lemma shift_symmetric (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (c : ℝ) :
    (shift T c).IsFormalAdjoint (shift T c) := by
  intro u v
  have hs := T.adjoint_isFormalAdjoint hT.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hT] at hs
  change ⟪T u + (c : ℂ) • (u : H), (v : H)⟫_ℂ =
    ⟪(u : H), T v + (c : ℂ) • (v : H)⟫_ℂ
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hs u v]

lemma shift_selfAdjoint (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (c : ℝ) :
    IsSelfAdjoint (shift T c) := by
  have hs := shift_symmetric T hT c
  have hd : Dense ((shift T c).domain : Set H) := hT.dense_domain
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.ext
  · apply Submodule.ext
    intro z
    constructor
    · intro hz
      have hz' : Continuous (fun u : T.domain => ⟪z, T u + (c : ℂ) • (u : H)⟫_ℂ) := hz
      have hc : Continuous (fun u : T.domain => ⟪z, (c : ℂ) • (u : H)⟫_ℂ) := by fun_prop
      have ht : z ∈ T.adjoint.domain := by
        change Continuous ((innerₛₗ ℂ z).comp T.toFun)
        convert hz'.sub hc using 1
        ext u
        simp
      change z ∈ T.domain
      simpa only [LinearPMap.isSelfAdjoint_def.mp hT] using ht
    · intro hz
      exact LinearPMap.mem_adjoint_domain_of_exists z
        ⟨shift T c ⟨z, hz⟩, hs ⟨z, hz⟩⟩
  · intro z hz hz'
    exact LinearPMap.adjoint_apply_eq hd ⟨z, hz⟩ (fun v => hs ⟨z, hz'⟩ v)

/-- A source nonnegative self-adjoint operator, with its actual domain. -/
structure NonnegativeOperator (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  op : H →ₗ.[ℂ] H
  selfAdjoint : IsSelfAdjoint op
  nonneg : ∀ u : op.domain, 0 ≤ (⟪(u : H), op u⟫_ℂ).re

/-- B+1 >= 1, constructed rather than supplied as a bounded energy operator. -/
def plusOne (B : NonnegativeOperator H) : PositiveOperator H where
  op := shift B.op 1
  selfAdjoint := shift_selfAdjoint B.op B.selfAdjoint 1
  lower := by
    change ∀ u : B.op.domain, ‖(u : H)‖ ^ 2 ≤
      (⟪(u : H), B.op u + (1 : ℂ) • (u : H)⟫_ℂ).re
    intro u
    rw [one_smul, inner_add_right, Complex.add_re]
    have he := norm_sq_eq_re_inner (𝕜 := ℂ) (u : H)
    change ‖(u : H)‖ ^ 2 = (⟪(u : H), (u : H)⟫_ℂ).re at he
    linarith [B.nonneg u, he]

end QuantumNLS.Ext005ShiftR114
#print axioms QuantumNLS.Ext005ShiftR114.shift_selfAdjoint
#print axioms QuantumNLS.Ext005ShiftR114.plusOne

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ShiftR114." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ShiftR114." then
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
  Lean.logInfo m!"R114 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
