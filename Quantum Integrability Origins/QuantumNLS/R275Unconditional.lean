import QuantumNLS.RiccatiDischarge
import QuantumNLS.SmoothScalarMomentsPhysical

/-! R-275B7656, moments:thm:moments, for every smooth periodic field.
The frozen smooth-field Riccati theorem discharges the prerequisite of
the frozen physical moment and expansion theorems. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace QuantumNLS.R275Unconditional
open QuantumNLS.ClassicalCharges QuantumNLS.CauchyUniqueness
open QuantumNLS.FullMass QuantumNLS.SmoothScalarMomentsAsymptotic
open QuantumNLS.SmoothScalarMomentsCauchy
open QuantumNLS.SmoothScalarMomentsPhysical

variable {L : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

/-- The printed all-smooth-scalar-moments theorem with its Riccati
prerequisite proved from smooth periodicity. -/
theorem R_275B7656 (κ : ℝ) (hκ : 0 < κ) (hf : SmoothPeriodic L f) :
    (∀ j : ℕ, (charge L κ f j).im = 0) ∧
    ∀ r : ℕ, Integrable (fun t : ℝ => |t| ^ r) (Mmeas κ (smoothL2 hf)) ∧
      ((∫ t : ℝ, t ^ r ∂(Mmeas κ (smoothL2 hf)) : ℝ) : ℂ) = charge L κ f (r + 1) := by
  exact all_smooth_scalar_moments κ hκ hf
    (QuantumNLS.RiccatiDischarge.riccati_printed_conclusion_of_smooth L hf)

/-- The physical expansion used in the printed proof, with the same
smooth-field discharge of its Riccati prerequisite. -/
theorem physical_expansion (κ : ℝ) (hκ : 0 < κ) (hf : SmoothPeriodic L f) :
    Expansion (fun n => cauchyTransform (Mmeas κ (smoothL2 hf)) (height n))
      (fun r => charge L κ f (r + 1)) := by
  exact QuantumNLS.SmoothScalarMomentsPhysical.physical_expansion κ hκ hf
    (QuantumNLS.RiccatiDischarge.riccati_printed_conclusion_of_smooth L hf)

#print axioms R_275B7656
#print axioms physical_expansion
end QuantumNLS.R275Unconditional

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut ownCount : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.R275Unconditional." ||
        n.toString.startsWith "_private.QuantumNLS.R275Unconditional." then
      pending := pending.push n
      ownCount := ownCount + 1
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
  Lean.logInfo m!"R275 unconditional audit PASS: {ownCount} own/generated constants; {seen.size} transitive constants; standard only."
