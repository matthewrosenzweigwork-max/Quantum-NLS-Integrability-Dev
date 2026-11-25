import QuantumNLS.Reg010LowKernel

/-! Tonelli and finiteness for the low positive spectral regularization. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace QuantumNLS.Reg010LowPositiveMoment
open QuantumNLS.Reg010LowKernel QuantumNLS.RootH1PositiveSpectral

def regularized (μ : Measure ℝ) (s Y : ℝ) : ℝ :=
  Y^(2*s-3) * ∫ x, kernel Y x ∂μ

theorem regularized_nonneg (μ : Measure ℝ) (s Y : ℝ) (hY : 0 ≤ Y) :
    0 ≤ regularized μ s Y :=
  mul_nonneg (Real.rpow_nonneg hY _) (integral_nonneg (kernel_nonneg Y))

theorem regularized_measurable (μ : Measure ℝ) [SFinite μ] (s : ℝ) :
    Measurable (regularized μ s) := by
  have hm : StronglyMeasurable (Function.uncurry kernel) := by
    apply Measurable.stronglyMeasurable
    unfold Function.uncurry kernel
    fun_prop
  exact (measurable_id.pow_const _).mul hm.integral_prod_right.measurable

theorem regularized_lintegral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (s Y : ℝ) (hY : 0 < Y) :
    ENNReal.ofReal (regularized μ s Y) =
      ∫⁻ x, ENNReal.ofReal (weightedKernel s Y x) ∂μ := by
  rw [regularized, ← integral_const_mul]
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (kernel_integrable hY μ).const_mul _
  · exact ae_of_all _ (fun x => weightedKernel_nonneg s Y x hY.le)

/-- Extended identity for each positive measure separately. It remains valid
when the moment is infinite; no subtraction of infinities is used. -/
theorem positive_extended_identity (μ : Measure ℝ) [IsFiniteMeasure μ]
    (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    (∫⁻ Y in Ioi 0, ENNReal.ofReal (regularized μ s Y)) =
      ENNReal.ofReal (normalization s) * ∫⁻ x, ENNReal.ofReal (|x|^(2*s)) ∂μ := by
  calc
    _ = ∫⁻ Y in Ioi 0, ∫⁻ x, ENNReal.ofReal (weightedKernel s Y x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
      exact regularized_lintegral μ s Y hY
    _ = ∫⁻ x, (∫⁻ Y in Ioi 0, ENNReal.ofReal (weightedKernel s Y x)) ∂μ := by
      apply lintegral_lintegral_swap
      apply Measurable.aemeasurable
      unfold weightedKernel kernel
      fun_prop
    _ = ∫⁻ x, ENNReal.ofReal (normalization s) * ENNReal.ofReal (|x|^(2*s)) ∂μ := by
      apply lintegral_congr
      intro x
      rw [← ofReal_integral_eq_lintegral_ofReal (weightedKernel_integrable s x hs hs')]
      · rw [scalar_identity s x hs hs', ENNReal.ofReal_mul (normalization_pos s hs hs').le]
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
        exact weightedKernel_nonneg s Y x hY.le
    _ = _ := lintegral_const_mul _ (by fun_prop)

/-- Moment finiteness is exactly integrability of its positive height
regularization. No regularity assumption on a field is involved. -/
theorem integrable_regularized_iff (μ : Measure ℝ) [IsFiniteMeasure μ]
    (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    IntegrableOn (regularized μ s) (Ioi 0) ↔ Integrable (fun x : ℝ => |x|^(2*s)) μ := by
  have hY : 0 ≤ᵐ[volume.restrict (Ioi 0)] regularized μ s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    exact regularized_nonneg μ s Y hY.le
  rw [IntegrableOn, ← lintegral_ofReal_ne_top_iff_integrable
    (regularized_measurable μ s).aestronglyMeasurable hY,
    positive_extended_identity μ s hs hs']
  have hc : ENNReal.ofReal (normalization s) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (normalization_pos s hs hs'))
  simp only [ne_eq, ENNReal.mul_eq_top, ENNReal.ofReal_ne_top, hc, not_false_eq_true,
    false_and, or_false, true_and]
  exact lintegral_ofReal_ne_top_iff_integrable
    (measurable_abs.pow_const _).aestronglyMeasurable
    (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg x) _))

/-- The finite specialization of the extended identity. -/
theorem positive_integral_identity (μ : Measure ℝ) [IsFiniteMeasure μ]
    (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    (∫ Y in Ioi 0, regularized μ s Y) =
      normalization s * ∫ x : ℝ, |x|^(2*s) ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae, positive_extended_identity μ s hs hs',
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (normalization_pos s hs hs').le,
    integral_eq_lintegral_of_nonneg_ae]
  · exact ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg x) _)
  · exact (measurable_abs.pow_const _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    exact regularized_nonneg μ s Y hY.le
  · exact (regularized_measurable μ s).aestronglyMeasurable

#print axioms regularized_nonneg
#print axioms regularized_measurable
#print axioms regularized_lintegral
#print axioms positive_extended_identity
#print axioms integrable_regularized_iff
#print axioms positive_integral_identity
end QuantumNLS.Reg010LowPositiveMoment

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowPositiveMoment." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowPositiveMoment." then
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
