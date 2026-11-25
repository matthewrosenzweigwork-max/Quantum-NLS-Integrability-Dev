import QuantumNLS.Ext005FormEmbeddingR114

/-! Identify the comparison energy with the actual B quadratic form on
its operator domain. This ties the form-order encoding to the source B. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory UniformSpace
namespace QuantumNLS.Ext005ComparisonIdentityR114
open Ext005OperatorFormR113 Ext005ShiftR114 Ext005FormEmbeddingR114
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma comparisonEnergy_operator (A : PositiveOperator H) (B : NonnegativeOperator H)
    (h : FormContained A (plusOne B)) (x : B.op.domain) (u : FormDomain A)
    (hu : inclusion A u = (x : H)) :
    comparisonEnergy A B h u = (⟪(x : H), B.op x⟫_ℂ).re := by
  let v : Core (plusOne B) := x
  have hv : comparison A (plusOne B) h u = (v : FormDomain (plusOne B)) := by
    apply inclusion_injective (plusOne B)
    rw [comparison_pair, inclusion_coe]
    exact hu
  rw [comparisonEnergy, hv, Completion.norm_coe, core_norm_sq, hu]
  change (⟪(x : H), B.op x + (1 : ℂ) • (x : H)⟫_ℂ).re - ‖(x : H)‖ ^ 2 = _
  rw [one_smul, inner_add_right, Complex.add_re]
  have he := norm_sq_eq_re_inner (𝕜 := ℂ) (x : H)
  change ‖(x : H)‖ ^ 2 = (⟪(x : H), (x : H)⟫_ℂ).re at he
  linarith

end QuantumNLS.Ext005ComparisonIdentityR114
#print axioms QuantumNLS.Ext005ComparisonIdentityR114.comparisonEnergy_operator

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ComparisonIdentityR114." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ComparisonIdentityR114." then
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
