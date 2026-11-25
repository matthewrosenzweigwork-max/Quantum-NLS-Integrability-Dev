import QuantumNLS.Reg010LowMomentReduction
import QuantumNLS.TerraMultiRound69FractionalCells

/-! The free real power moment on the actual DEF-002 Sobolev carrier. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open MeasureTheory
namespace QuantumNLS.Reg010LowFreeSobolev
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Fourier
open QuantumNLS.Sobolev QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b
variable {L : ℝ} [Fact (0 < L)]

theorem free_power_integrable_iff_summable (u : L2T L) (s : ℝ) :
    Integrable (fun t : ℝ => |t|^(2*s)) (freeMeasure L u) ↔
      Summable (fun n : ℤ => |QuantumNLS.Fourier.freq L n|^(2*s) * ‖fourierL2 L u n‖^2) := by
  change Integrable (fun t : ℝ => |t|^(2*s)) (Measure.sum (fun n : ℤ =>
    ENNReal.ofReal (‖coeff L (u : AddCircle L → ℂ) n‖^2) •
      Measure.dirac (2 * Real.pi * n / L))) ↔ _
  rw [integrable_sum_dirac_iff (fun n => by simp)]
  apply summable_congr
  intro n
  rw [ENNReal.toReal_ofReal (sq_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← fourierL2_apply]
  simp only [QuantumNLS.Fourier.freq]
  ring

/-- A genuine real-order Sobolev criterion, using the mass to add the shift. -/
theorem free_power_integrable_iff_hsq (u : L2T L) (s : ℝ) (hs : 0 < s) :
    Integrable (fun t : ℝ => |t|^(2*s)) (freeMeasure L u) ↔
      hsq L s (fun n => coeff L (u : AddCircle L → ℂ) n) ≠ ⊤ := by
  haveI := QuantumNLS.Reg010LowBasic.free_finite u
  have hshift := QuantumNLS.TerraMultiRound69FractionalCells.bounded_displacement_rpow
    (freeMeasure L u) (2*s) (by positivity) (fun t : ℝ => |t|) (fun t : ℝ => 1+|t|)
    measurable_abs.aestronglyMeasurable (measurable_const.add measurable_abs).aestronglyMeasurable
    1 (by apply ae_of_all; intro t; simp)
  have hn : ∀ t : ℝ, abs (1+|t|) = 1+|t| := fun t => abs_of_nonneg (by positivity)
  simp only [Real.norm_eq_abs, abs_abs, hn] at hshift
  rw [hshift]
  have hdirac : Integrable (fun t : ℝ => (1+|t|)^(2*s)) (freeMeasure L u) ↔
      Summable (fun n : ℤ => wt L s n * ‖coeff L (u : AddCircle L → ℂ) n‖^2) := by
    change Integrable (fun t : ℝ => (1+|t|)^(2*s)) (Measure.sum (fun n : ℤ =>
      ENNReal.ofReal (‖coeff L (u : AddCircle L → ℂ) n‖^2) •
        Measure.dirac (2*Real.pi*n/L))) ↔ _
    rw [integrable_sum_dirac_iff (fun n => by simp)]
    apply summable_congr
    intro n
    rw [ENNReal.toReal_ofReal (sq_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    unfold wt QuantumNLS.RiccatiSobolevE1.freq
    ring
  rw [hdirac]
  exact ⟨fun h => h.tsum_ofReal_ne_top, fun h => (hsq_summable_eq h).1⟩

/-- Bundled membership in the accepted DEF-002 field space, at every
positive real order. -/
theorem free_power_integrable_iff_H02 (u : L2T L) (s : ℝ) (hs : 0 < s) :
    Integrable (fun t : ℝ => |t|^(2*s)) (freeMeasure L u) ↔
      ∃ v : H02 L s, v.val = u := by
  rw [free_power_integrable_iff_hsq u s hs]
  constructor
  · intro h
    have hm : u ∈ fieldSub L (def002 L s) := by
      change Summable (fun n : ℤ => sobolevWeight L s n * ‖fourierL2 L u n‖^2)
      simpa only [wt, QuantumNLS.RiccatiSobolevE1.freq, sobolevWeight, ← fourierL2_apply] using
        (hsq_summable_eq h).1
    exact ⟨(⟨u,hm⟩ : H02 L s), rfl⟩
  · rintro ⟨v,rfl⟩
    have hm := (toSeq L (def002 L s) v).summable
    change Summable (fun n : ℤ => sobolevWeight L s n * ‖fourierL2 L v.val n‖^2) at hm
    apply Summable.tsum_ofReal_ne_top
    simpa only [toSeq_val, def002, wt, QuantumNLS.RiccatiSobolevE1.freq, sobolevWeight,
      ← fourierL2_apply] using hm

#print axioms free_power_integrable_iff_summable
#print axioms free_power_integrable_iff_hsq
#print axioms free_power_integrable_iff_H02
end QuantumNLS.Reg010LowFreeSobolev

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowFreeSobolev." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowFreeSobolev." then
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
  Lean.logInfo m!"Round46 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
