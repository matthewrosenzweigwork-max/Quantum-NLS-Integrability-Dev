import QuantumNLS.RootH1Ratio

/-! Bounded spectral regularization at arbitrary real height, without any
second-moment assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open QuantumNLS.PhysicalTensor QuantumNLS.CauchyUniqueness
namespace QuantumNLS.RootH1PositiveSpectral

def kernel (Y t : ℝ) : ℝ := Y^2*t^2/(Y^2+t^2)

lemma kernel_nonneg (Y t : ℝ) : 0 ≤ kernel Y t := by unfold kernel; positivity

lemma kernel_integrable {Y : ℝ} (hY : 0 < Y) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (kernel Y) μ := by
  have hc : Continuous (kernel Y) := by
    unfold kernel
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  refine (integrable_const (Y^2)).mono' hc.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg _ _)]
  unfold kernel
  apply (div_le_iff₀ (by positivity : 0 < Y^2+t^2)).mpr
  nlinarith [sq_nonneg Y]

lemma pk_integrable {Y : ℝ} (hY : 0 < Y) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun t : ℝ => pk Y (-t)) μ := by
  refine (integrable_const (Y⁻¹)).mono'
    ((continuous_pk hY).comp continuous_neg).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs,abs_of_nonneg (pk_nonneg hY _)]
  unfold pk
  apply (div_le_iff₀ (by positivity : 0 < Y^2+(-t)^2)).mpr
  have hpos : 0 ≤ Y⁻¹ := inv_nonneg.mpr hY.le
  have he : Y⁻¹*Y^2 = Y := by field_simp
  nlinarith [mul_nonneg hpos (sq_nonneg (-t))]

lemma spectral_identity {Y : ℝ} (hY : 0 < Y) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∫ t, kernel Y t ∂μ) = Y^2*(μ.real univ+Y*(cauchyTransform μ ((Y:ℂ)*Complex.I)).im) := by
  have hh := im_cauchy μ hY 0
  simp only [Complex.ofReal_zero,zero_add,poisson,zero_sub] at hh
  have he : ∀ t : ℝ, kernel Y t = Y^2*(1-Y*pk Y (-t)) := by
    intro t
    unfold kernel pk
    have hn : Y^2+(-t)^2 ≠ 0 := by positivity
    rw [neg_sq]
    field_simp
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_sub (integrable_const _) ((pk_integrable hY μ).const_mul Y),
    integral_const,smul_eq_mul,mul_one,integral_const_mul]
  rw [hh]
  ring

lemma physical_identity {L κ Y : ℝ} [Fact (0 < L)] (hY : 0 < Y) (u : L2T L) :
    (∫ t, kernel Y t ∂(QuantumNLS.FullMass.Mmeas κ u)) =
      Y^2*(‖u‖^2+Y*(cauchyTransform (QuantumNLS.FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I)).im) := by
  rw [spectral_identity hY]
  congr 2
  rw [measureReal_def,QuantumNLS.FullMass.Mmeas_univ,ENNReal.toReal_ofReal (sq_nonneg _)]

#print axioms kernel_nonneg
#print axioms kernel_integrable
#print axioms pk_integrable
#print axioms spectral_identity
#print axioms physical_identity
end QuantumNLS.RootH1PositiveSpectral

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1PositiveSpectral." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1PositiveSpectral." then
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
