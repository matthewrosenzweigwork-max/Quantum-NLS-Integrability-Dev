import QuantumNLS.Reg010LowNormalization
import QuantumNLS.Reg010LowIdentity

/-! Literal sine normalization and the printed finite and extended identities. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.Reg010LowPrinted
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Reg010LowBasic
open QuantumNLS.Reg010LowKernel QuantumNLS.Reg010LowCorrection QuantumNLS.Reg010LowIdentity
variable {L : ℝ} [Fact (0 < L)]

theorem coefficient_normalization (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    coefficient s * normalization s = 1 := by
  have hsin : 0 < Real.sin (Real.pi*s) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hs) (by nlinarith [Real.pi_pos])
  rw [QuantumNLS.Reg010LowNormalization.normalization_eq s hs hs', coefficient]
  field_simp

/-- The literal printed scalar kernel formula with c_s=2 sin(pi s)/pi. -/
theorem positive_fractional (s x : ℝ) (hs : 0 < s) (hs' : s < 1) :
    |x|^(2*s) = coefficient s * ∫ Y in Ioi 0, Y^(2*s-3) *
      QuantumNLS.RootH1PositiveSpectral.kernel Y x := by
  change _ = coefficient s * ∫ Y in Ioi 0, weightedKernel s Y x
  rw [scalar_identity s x hs hs', ← mul_assoc, coefficient_normalization s hs hs', one_mul]

/-- The finite low-order identity on all L², with exactly the frozen printed J. -/
theorem all_L2_fractional_identity (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1/2)
    (hm : Integrable (fun x : ℝ => |x|^(2*s)) (PhysicalQuantumMeasure.measure hκ u)) :
    (∫ x : ℝ, |x|^(2*s) ∂PhysicalQuantumMeasure.measure hκ u) =
      (∫ x : ℝ, |x|^(2*s) ∂freeMeasure L u) + J κ hκ s u := by
  have h := congrArg (fun z => coefficient s*z) ((all_L2_low_identity κ hκ u s hs hs').2 hm)
  rw [← mul_assoc, coefficient_normalization s hs (by linarith), one_mul] at h
  change _ - _ = J κ hκ s u at h
  linarith

/-- The finite identity on native L⁴, for the full open low-order interval. -/
theorem L4_fractional_identity (κ : ℝ) (hκ : 0 < κ)
    (u : QuantumNLS.Reg010LowL4Space.L4T L)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1)
    (hm : Integrable (fun x : ℝ => |x|^(2*s))
      (PhysicalQuantumMeasure.measure hκ (QuantumNLS.Reg010LowL4Space.toL2 u))) :
    let v := QuantumNLS.Reg010LowL4Space.toL2 u
    (∫ x : ℝ, |x|^(2*s) ∂PhysicalQuantumMeasure.measure hκ v) =
      (∫ x : ℝ, |x|^(2*s) ∂freeMeasure L v) + J κ hκ s v := by
  have h := congrArg (fun z => coefficient s*z) ((L4_low_identity κ hκ u s hs hs').2 hm)
  rw [← mul_assoc, coefficient_normalization s hs hs', one_mul] at h
  change _ - _ = J κ hκ s (QuantumNLS.Reg010LowL4Space.toL2 u) at h
  dsimp only
  linarith

/-- Both positive moments are infinite when finiteness fails, as required
by the extended interpretation. -/
theorem all_L2_infinite_moments (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1/2)
    (hm : ¬Integrable (fun x : ℝ => |x|^(2*s)) (PhysicalQuantumMeasure.measure hκ u)) :
    (∫⁻ x : ℝ, ENNReal.ofReal (|x|^(2*s)) ∂PhysicalQuantumMeasure.measure hκ u) = ⊤ ∧
    (∫⁻ x : ℝ, ENNReal.ofReal (|x|^(2*s)) ∂freeMeasure L u) = ⊤ := by
  have hf := mt ((all_L2_low_identity κ hκ u s hs hs').1.mpr) hm
  constructor
  · by_contra hn
    exact hm ((lintegral_ofReal_ne_top_iff_integrable
      (measurable_abs.pow_const _).aestronglyMeasurable
      (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg x) _))).mp hn)
  · by_contra hn
    exact hf ((lintegral_ofReal_ne_top_iff_integrable
      (measurable_abs.pow_const _).aestronglyMeasurable
      (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg x) _))).mp hn)

theorem L4_infinite_moments (κ : ℝ) (hκ : 0 < κ)
    (u : QuantumNLS.Reg010LowL4Space.L4T L)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1)
    (hm : ¬Integrable (fun x : ℝ => |x|^(2*s))
      (PhysicalQuantumMeasure.measure hκ (QuantumNLS.Reg010LowL4Space.toL2 u))) :
    let v := QuantumNLS.Reg010LowL4Space.toL2 u
    (∫⁻ x : ℝ, ENNReal.ofReal (|x|^(2*s)) ∂PhysicalQuantumMeasure.measure hκ v) = ⊤ ∧
    (∫⁻ x : ℝ, ENNReal.ofReal (|x|^(2*s)) ∂freeMeasure L v) = ⊤ := by
  have hf := mt ((L4_low_identity κ hκ u s hs hs').1.mpr) hm
  constructor
  · by_contra hn
    exact hm ((lintegral_ofReal_ne_top_iff_integrable
      (measurable_abs.pow_const _).aestronglyMeasurable
      (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg x) _))).mp hn)
  · by_contra hn
    exact hf ((lintegral_ofReal_ne_top_iff_integrable
      (measurable_abs.pow_const _).aestronglyMeasurable
      (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg x) _))).mp hn)

#print axioms coefficient_normalization
#print axioms positive_fractional
#print axioms all_L2_fractional_identity
#print axioms L4_fractional_identity
#print axioms all_L2_infinite_moments
#print axioms L4_infinite_moments
end QuantumNLS.Reg010LowPrinted

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowPrinted." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowPrinted." then
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
