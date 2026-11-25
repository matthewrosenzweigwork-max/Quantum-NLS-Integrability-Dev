import QuantumNLS.Reg010LowIdentity
import QuantumNLS.Reg010LowFreeSobolev

/-! The unconditional one-third Sobolev step from a finite higher physical moment. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.Reg010LowBootstrap
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
variable {L : ℝ} [Fact (0 < L)]

/-- The complete low-range membership criterion on the actual L² carrier. -/
theorem low_characterization (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1/2) :
    Integrable (fun t : ℝ => |t|^(2*s)) (PhysicalQuantumMeasure.measure hκ u) ↔
      ∃ v : H02 L s, v.val = u :=
  (QuantumNLS.Reg010LowIdentity.all_L2_low_identity κ hκ u s hs hs').1.trans
    (QuantumNLS.Reg010LowFreeSobolev.free_power_integrable_iff_H02 u s hs)

/-- The full low-order membership criterion on the native L4 carrier. -/
theorem L4_characterization (κ : ℝ) (hκ : 0 < κ)
    (u : QuantumNLS.Reg010LowL4Space.L4T L) (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    let v := QuantumNLS.Reg010LowL4Space.toL2 u
    Integrable (fun t : ℝ => |t|^(2*s)) (PhysicalQuantumMeasure.measure hκ v) ↔
      ∃ w : H02 L s, w.val = v :=
  (QuantumNLS.Reg010LowIdentity.L4_low_identity κ hκ u s hs hs').1.trans
    (QuantumNLS.Reg010LowFreeSobolev.free_power_integrable_iff_H02 _ s hs)

/-- No auxiliary regularity or lower-moment hypothesis is imposed. The
higher physical moment alone supplies the actual H^(1/3) field. -/
theorem higher_moment_one_third (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 1/3 ≤ s)
    (hm : Integrable (fun t : ℝ => |t|^(2*s)) (PhysicalQuantumMeasure.measure hκ u)) :
    ∃ v : H02 L (1/3), v.val = u := by
  have h := (QuantumNLS.Reg010LowMomentReduction.physical_one_third_moment hκ u s hs hm).1
  have he : (2:ℝ)*(1/3) = 2/3 := by norm_num
  apply (low_characterization κ hκ u (1/3) (by norm_num) (by norm_num)).mp
  simpa only [he] using h

/-- The same conclusion in the extended Fourier norm interface used by
terra_multi. -/
theorem higher_moment_one_third_hsq (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 1/3 ≤ s)
    (hm : Integrable (fun t : ℝ => |t|^(2*s)) (PhysicalQuantumMeasure.measure hκ u)) :
    QuantumNLS.RiccatiSobolevE1.hsq L (1/3)
      (fun n => coeff L (u : AddCircle L → ℂ) n) ≠ ⊤ := by
  have h := (QuantumNLS.Reg010LowMomentReduction.physical_one_third_moment hκ u s hs hm).1
  have he : (2:ℝ)*(1/3) = 2/3 := by norm_num
  apply (QuantumNLS.Reg010LowFreeSobolev.free_power_integrable_iff_hsq u (1/3)
    (by norm_num)).mp
  apply (QuantumNLS.Reg010LowIdentity.all_L2_low_identity κ hκ u (1/3)
    (by norm_num) (by norm_num)).1.mp
  simpa only [he] using h

#print axioms L4_characterization
#print axioms low_characterization
#print axioms higher_moment_one_third
#print axioms higher_moment_one_third_hsq
end QuantumNLS.Reg010LowBootstrap

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowBootstrap." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowBootstrap." then
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
