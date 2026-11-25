import Mathlib

/-! A finite exceptional set does not obstruct monotonicity of a continuous real function. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set
namespace QuantumNLS.FiniteExceptionalMonotonicity

theorem image_le (f : ℝ → ℝ) (hc : Continuous f) (S : Finset ℝ) :
    ∀ a b : ℝ, a ≤ b →
      (∀ x ∈ Ioo a b, x ∉ S → DifferentiableAt ℝ f x) →
      (∀ x ∈ Ioo a b, x ∉ S → 0 ≤ deriv f x) → f a ≤ f b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro a b hab hd hn
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hc.continuousOn _ _ ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx (by simp)).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact hn x hx (by simp)
  | @insert c S hcS ih =>
    intro a b hab hd hn
    by_cases hm : a < c ∧ c < b
    · apply (ih a c hm.1.le _ _).trans (ih c b hm.2.le _ _)
      · intro x hx hs
        exact hd x ⟨hx.1, hx.2.trans hm.2⟩ (by simp [hs, ne_of_lt hx.2])
      · intro x hx hs
        exact hn x ⟨hx.1, hx.2.trans hm.2⟩ (by simp [hs, ne_of_lt hx.2])
      · intro x hx hs
        exact hd x ⟨hm.1.trans hx.1, hx.2⟩ (by simp [hs, ne_of_gt hx.1])
      · intro x hx hs
        exact hn x ⟨hm.1.trans hx.1, hx.2⟩ (by simp [hs, ne_of_gt hx.1])
    · apply ih a b hab
      · intro x hx hs
        apply hd x hx
        have hn : x ≠ c := by intro he; subst x; exact hm hx
        simp [hs, hn]
      · intro x hx hs
        apply hn x hx
        have hnc : x ≠ c := by intro he; subst x; exact hm hx
        simp [hs, hnc]

end QuantumNLS.FiniteExceptionalMonotonicity

#print axioms QuantumNLS.FiniteExceptionalMonotonicity.image_le

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.FiniteExceptionalMonotonicity." then
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
