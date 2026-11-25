import QuantumNLS.Local001PotentialOperatorB

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace QuantumNLS.ResetFreeResolventLOCAL001
open CompletionB
/-- The complete `lem:reset-free-resolvent` estimate on the source parity contour. -/
theorem reset_free_resolvent_estimates {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hL : 0 < L) (hκ : 0 < κ) (n : ℤ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) :
    ‖LocalSpectral.resolvent L κ (fun _ => 0) (LocalSpectral.parity n) z‖ ≤ r⁻¹ ∧
    (∀ f : VectorInterval L, ∀ᵐ x ∂(LocalSpectral.μI L),
      ‖LocalSpectral.resolvent L κ (fun _ => 0) (LocalSpectral.parity n) z f x‖ ≤
        resolventConstant L r * ‖f‖) ∧
    resolventConstant L r ^ 2 = L⁻¹ *
      (r⁻¹ ^ 2 + 2 * ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2) ∧
    ‖potentialResolvent κ hκ.le hL n hr hsmall hz u‖ ≤
      2 * Real.sqrt κ * resolventConstant L r * ‖u‖ := by
  refine ⟨sourceResolvent_norm_le hL κ n hr hsmall hz, ?_, ?_, ?_⟩
  · intro f
    exact sourceResolvent_ae_sup_bound hL κ n hr hsmall hz f
  · exact resolventConstant_sq hL
  · exact potentialResolvent_norm_le κ hκ.le hL n hr hsmall hz u


#print axioms reset_free_resolvent_estimates
#print axioms CompletionB.sourceResolvent_eq_candidate
#print axioms CompletionB.potentialResolvent_norm_le
end QuantumNLS.ResetFreeResolventLOCAL001

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ResetFreeResolventLOCAL001." ||
        n.toString.startsWith "_private.QuantumNLS.Local001" then
      pending := pending.push n
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
  Lean.logInfo m!"Local001FinalB audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
