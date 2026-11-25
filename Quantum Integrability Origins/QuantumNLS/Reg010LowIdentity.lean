import QuantumNLS.Reg010LowPositiveMoment
import QuantumNLS.Reg010LowL4Correction

/-! The extended low moment comparison, without subtracting infinite moments. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.Reg010LowIdentity
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Reg010LowBasic
open QuantumNLS.Reg010LowKernel QuantumNLS.Reg010LowPositiveMoment
variable {L : ℝ} [Fact (0 < L)]

/-- An integrable signed difference transfers finiteness in both directions. -/
theorem integrable_iff_of_difference {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hd : Integrable (fun x => f x - g x) μ) : Integrable f μ ↔ Integrable g μ := by
  constructor
  · intro hf
    convert hf.sub hd using 1
    funext x
    simp
  · intro hg
    convert hd.add hg using 1
    funext x
    simp

/-- A general finite-measure comparison theorem. Its hypothesis is absolute
integrability of the signed regularization, not of either desired moment. -/
theorem moment_comparison (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : ℝ) (hs : 0 < s) (hs' : s < 1)
    (hd : IntegrableOn (fun Y => regularized μ s Y - regularized ν s Y) (Ioi 0)) :
    (Integrable (fun x : ℝ => |x|^(2*s)) μ ↔
      Integrable (fun x : ℝ => |x|^(2*s)) ν) ∧
    (Integrable (fun x : ℝ => |x|^(2*s)) μ →
      normalization s * ((∫ x : ℝ, |x|^(2*s) ∂μ) - ∫ x : ℝ, |x|^(2*s) ∂ν) =
        ∫ Y in Ioi 0, regularized μ s Y - regularized ν s Y) := by
  have hi := integrable_iff_of_difference hd
  have hiff := (integrable_regularized_iff μ s hs hs').symm.trans
    (hi.trans (integrable_regularized_iff ν s hs hs'))
  refine ⟨hiff, ?_⟩
  intro hm
  rw [integral_sub ((integrable_regularized_iff μ s hs hs').mpr hm)
    ((integrable_regularized_iff ν s hs hs').mpr (hiff.mp hm)),
    positive_integral_identity μ s hs hs', positive_integral_identity ν s hs hs']
  ring

theorem physical_free_difference (κ : ℝ) (hκ : 0 < κ) (u : L2T L) (s Y : ℝ) :
    regularized (PhysicalQuantumMeasure.measure hκ u) s Y - regularized (freeMeasure L u) s Y =
      Y^(2*s-3) * correction κ hκ u Y := by
  unfold regularized correction
  ring

/-- The all-L² low-range criterion and its finite difference identity.
The normalization is fully defined by a convergent positive scalar integral. -/
theorem all_L2_low_identity (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1/2) :
    (Integrable (fun x : ℝ => |x|^(2*s)) (PhysicalQuantumMeasure.measure hκ u) ↔
      Integrable (fun x : ℝ => |x|^(2*s)) (freeMeasure L u)) ∧
    (Integrable (fun x : ℝ => |x|^(2*s)) (PhysicalQuantumMeasure.measure hκ u) →
      normalization s * ((∫ x : ℝ, |x|^(2*s) ∂PhysicalQuantumMeasure.measure hκ u) -
        ∫ x : ℝ, |x|^(2*s) ∂freeMeasure L u) =
        ∫ Y in Ioi 0, Y^(2*s-3) * correction κ hκ u Y) := by
  haveI := free_finite u
  have hd := QuantumNLS.Reg010LowCorrection.weighted_correction_integrable κ hκ s hs hs' u
  have he : (fun Y => regularized (PhysicalQuantumMeasure.measure hκ u) s Y -
      regularized (freeMeasure L u) s Y) = (fun Y => Y^(2*s-3)*correction κ hκ u Y) :=
    funext (physical_free_difference κ hκ u s)
  have h := moment_comparison (PhysicalQuantumMeasure.measure hκ u) (freeMeasure L u)
    s hs (by linarith) (by rw [he]; exact hd)
  simpa only [he] using h

/-- The same criterion holds on native L⁴ throughout 0<s<1. -/
theorem L4_low_identity (κ : ℝ) (hκ : 0 < κ) (u : QuantumNLS.Reg010LowL4Space.L4T L)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    let v := QuantumNLS.Reg010LowL4Space.toL2 u
    (Integrable (fun x : ℝ => |x|^(2*s)) (PhysicalQuantumMeasure.measure hκ v) ↔
      Integrable (fun x : ℝ => |x|^(2*s)) (freeMeasure L v)) ∧
    (Integrable (fun x : ℝ => |x|^(2*s)) (PhysicalQuantumMeasure.measure hκ v) →
      normalization s * ((∫ x : ℝ, |x|^(2*s) ∂PhysicalQuantumMeasure.measure hκ v) -
        ∫ x : ℝ, |x|^(2*s) ∂freeMeasure L v) =
        ∫ Y in Ioi 0, Y^(2*s-3) * correction κ hκ v Y) := by
  let v := QuantumNLS.Reg010LowL4Space.toL2 u
  haveI := free_finite v
  have hd := QuantumNLS.Reg010LowL4Correction.weighted_correction_integrable κ hκ s hs hs' u
  have he : (fun Y => regularized (PhysicalQuantumMeasure.measure hκ v) s Y -
      regularized (freeMeasure L v) s Y) = (fun Y => Y^(2*s-3)*correction κ hκ v Y) :=
    funext (physical_free_difference κ hκ v s)
  have h := moment_comparison (PhysicalQuantumMeasure.measure hκ v) (freeMeasure L v)
    s hs hs' (by rw [he]; exact hd)
  simpa only [he] using h

#print axioms integrable_iff_of_difference
#print axioms moment_comparison
#print axioms physical_free_difference
#print axioms all_L2_low_identity
#print axioms L4_low_identity
end QuantumNLS.Reg010LowIdentity

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowIdentity." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowIdentity." then
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
