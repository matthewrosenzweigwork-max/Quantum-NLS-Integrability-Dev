import QuantumNLS.Reg010LowCorrection

/-! The unconditional moment reduction used by the printed one-third
bootstrap. This file does not claim the missing Sobolev embedding. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.Reg010LowMomentReduction
open QuantumNLS.PhysicalTensor

theorem lower_power_le (x p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) :
    |x| ^ p ≤ 1 + |x| ^ q := by
  by_cases hx : |x| ≤ 1
  · have h := Real.rpow_le_one (abs_nonneg x) hx hp
    exact h.trans (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg x) q))
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hpq
    exact h.trans (le_add_of_nonneg_left (by norm_num))

theorem lower_moment_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q)
    (hq : Integrable (fun x : ℝ => |x| ^ q) μ) :
    Integrable (fun x : ℝ => |x| ^ p) μ ∧
      (∫ x : ℝ, |x| ^ p ∂μ) ≤ μ.real univ + ∫ x : ℝ, |x| ^ q ∂μ := by
  have hi : Integrable (fun x : ℝ => |x| ^ p) μ := by
    apply ((integrable_const (1 : ℝ)).add hq).mono'
      (measurable_abs.pow_const p).aestronglyMeasurable
    filter_upwards with x
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) p)] using
      lower_power_le x p q hp hpq
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x : ℝ, 1 + |x| ^ q ∂μ := integral_mono hi
      ((integrable_const (1 : ℝ)).add hq) (fun x => lower_power_le x p q hp hpq)
    _ = _ := by rw [integral_add (integrable_const _) hq]; simp

/-- A finite higher physical moment automatically supplies the 2/3 moment.
There is no additional moment or field regularity hypothesis. -/
theorem physical_one_third_moment {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)
    (u : L2T L) (s : ℝ) (hs : 1 / 3 ≤ s)
    (hm : Integrable (fun t : ℝ => |t| ^ (2 * s)) (PhysicalQuantumMeasure.measure hκ u)) :
    Integrable (fun t : ℝ => |t| ^ (2 / 3 : ℝ)) (PhysicalQuantumMeasure.measure hκ u) ∧
      (∫ t : ℝ, |t| ^ (2 / 3 : ℝ) ∂PhysicalQuantumMeasure.measure hκ u) ≤
        ‖u‖ ^ 2 + ∫ t : ℝ, |t| ^ (2 * s) ∂PhysicalQuantumMeasure.measure hκ u := by
  have h := lower_moment_integrable (PhysicalQuantumMeasure.measure hκ u)
    (2 / 3) (2 * s) (by norm_num) (by linarith) hm
  rw [measureReal_def, PhysicalQuantumMeasure.full_mass] at h
  exact h

#print axioms lower_power_le
#print axioms lower_moment_integrable
#print axioms physical_one_third_moment
end QuantumNLS.Reg010LowMomentReduction

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowMomentReduction." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowMomentReduction." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Round45 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
