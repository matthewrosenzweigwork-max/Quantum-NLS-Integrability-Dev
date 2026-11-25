import QuantumNLS.Ext005ForwardContractR37b

/-! The forward LNS Theorem 8 contract, with owner D3 uniqueness.
All times are finite and initial data are at the left endpoint. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005ContractR39b
open Ext005OperatorFormR113 Ext005SourceIntervalR32b Ext005ForwardContractR37b
open Ext005SourceBoundsR36b
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- EXT-005: source hypotheses give forward existence, an explicit uniform
Q(A) bound, the original weak equation, norm conservation, and uniqueness
in exactly D3 on this interval. No right-endpoint existence is asserted. -/
theorem EXT005_contract (A : PositiveOperator H) (a b : ℝ)
    (S : SourceOn A a b) (hab : a < b) (u₀ : FormDomain A) :
    ∃ v : ℝ → FormDomain A,
      v a = u₀ ∧ (∀ t ∈ Icc a b, ‖v t‖ ≤ forwardRadius A a b S u₀) ∧
      D3On A a b S (fun t => inclusion A (v t)) ∧
      ‖inclusion A (v b)‖ = ‖inclusion A u₀‖ ∧
      ∀ y : ℝ → H, D3On A a b S y → y a = inclusion A u₀ →
        ∀ t ∈ Icc a b, y t = inclusion A (v t) :=
  EXT005_forward_contract A a b S hab u₀

end QuantumNLS.Ext005ContractR39b
#print axioms QuantumNLS.Ext005ContractR39b.EXT005_contract

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ContractR39b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ContractR39b." then
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
  Lean.logInfo m!"R39b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
