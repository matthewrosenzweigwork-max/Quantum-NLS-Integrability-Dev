import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Author sol_ext_b, Round 3. C01 spectral-measure core. These are actual
exponential integrals against a positive measure, with only its first moment
assumed integrable. No operator-domain differentiability or second moment is
used. The arbitrary unbounded selfadjoint spectral representation is a separate
remaining obligation; it is not a premise disguised as the conclusion. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal
namespace QuantumNLS.Ext025B3FormSpectral

def phase (t x : ℝ) : ℂ := Complex.exp (Complex.I * (-(t * x) : ℝ))

theorem phase_norm (t x : ℝ) : ‖phase t x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_sub_bound (t x : ℝ) : ‖phase t x - 1‖ ≤ |t| * |x| := by
  simpa [phase, norm_neg, Real.norm_eq_abs, abs_mul] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(t * x)))

theorem phase_sub_two (t x : ℝ) : ‖phase t x - 1‖ ≤ 2 := by
  have h := norm_sub_le (phase t x) (1 : ℂ)
  norm_num [phase_norm] at h ⊢
  exact h

/-- The sharp first-moment majorant used for the norm estimate. -/
theorem square_bound (t x : ℝ) (hx : 0 ≤ x) :
    ‖phase t x - 1‖ ^ 2 / |t| ≤ 2 * x := by
  by_cases ht : t = 0
  · simp [ht]; positivity
  have ha : 0 < |t| := abs_pos.mpr ht
  apply (div_le_iff₀ ha).mpr
  have h₁ := phase_sub_two t x
  have h₂ := phase_sub_bound t x
  rw [abs_of_nonneg hx] at h₂
  have hn := norm_nonneg (phase t x - 1)
  nlinarith

theorem quotient_bound (t x : ℝ) :
    ‖(phase t x - 1) / (t : ℂ)‖ ≤ |x| := by
  by_cases ht : t = 0
  · simp [ht]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  exact (div_le_iff₀ (abs_pos.mpr ht)).mpr (by
    simpa [mul_comm] using phase_sub_bound t x)

/-- Both signs of real time are included. -/
theorem quotient_limit (x : ℝ) :
    Tendsto (fun t : ℝ => (phase t x - 1) / (t : ℂ)) (𝓝[≠] 0)
      (𝓝 (-Complex.I * (x : ℂ))) := by
  have hd : HasDerivAt (fun t : ℝ => phase t x) (-Complex.I * (x : ℂ)) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).mul_const x).neg.ofReal_comp.const_mul
      Complex.I).cexp
    convert h using 1 <;> simp [phase]
  simpa [phase, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero

theorem square_limit (x : ℝ) :
    Tendsto (fun t : ℝ => ‖phase t x - 1‖ ^ 2 / |t|) (𝓝[≠] 0) (𝓝 0) := by
  have h := ((quotient_limit x).norm.pow 2).mul
    ((continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
  simp only [abs_zero, mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow]
  field_simp

variable {μ : Measure ℝ≥0}

/-- Actual scalar spectral integral; a first moment, not a second moment, suffices. -/
theorem «FIN-EXT025-C01-spectral-derivative»
    (hm : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ≥0, (phase t x - 1) / (t : ℂ) ∂μ)
      (𝓝[≠] 0) (𝓝 (-Complex.I * (∫ x : ℝ≥0, (x : ℝ) ∂μ : ℂ))) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝[≠] (0 : ℝ)) (fun x : ℝ≥0 => (x : ℝ))
    (F := fun t x => (phase t x - 1) / (t : ℂ))
    (f := fun x => -Complex.I * (x : ℂ))
    (Eventually.of_forall fun t => by
      apply Continuous.aestronglyMeasurable
      unfold phase
      fun_prop)
    (Eventually.of_forall fun t => Eventually.of_forall fun x => by
      simpa only [abs_of_nonneg x.coe_nonneg] using quotient_bound t x)
    hm (Eventually.of_forall fun x => quotient_limit x)
  simpa only [integral_const_mul, integral_complex_ofReal] using h

/-- Squared norm density is o(|t|), with the exact 2λ majorant. -/
theorem «FIN-EXT025-C01-spectral-square»
    (hm : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ≥0, ‖phase t x - 1‖ ^ 2 / |t| ∂μ)
      (𝓝[≠] 0) (𝓝 0) := by
  simpa using tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝[≠] (0 : ℝ)) (fun x : ℝ≥0 => 2 * (x : ℝ))
    (F := fun t x => ‖phase t x - 1‖ ^ 2 / |t|) (f := fun _ => (0 : ℝ))
    (Eventually.of_forall fun t => by
      apply Continuous.aestronglyMeasurable
      unfold phase
      fun_prop)
    (Eventually.of_forall fun t => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact square_bound t x x.coe_nonneg)
    (hm.const_mul 2) (Eventually.of_forall fun x => square_limit x)

/-- The genuine derivative of the integrated spectral increment at zero. -/
theorem spectral_hasDerivAt
    (hm : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) :
    HasDerivAt (fun t : ℝ => ∫ x : ℝ≥0, phase t x - 1 ∂μ)
      (-Complex.I * (∫ x : ℝ≥0, (x : ℝ) ∂μ : ℂ)) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simpa only [zero_add, phase, zero_mul, neg_zero, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, sub_self, integral_zero, sub_zero,
    smul_eq_mul, Complex.real_smul, div_eq_mul_inv, integral_const_mul, Complex.ofReal_inv, mul_comm]
    using «FIN-EXT025-C01-spectral-derivative» hm

/-- The spectral square-root norm is o(sqrt(|t|)), from both sides. -/
theorem spectral_sqrt_ratio
    (hm : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) :
    Tendsto (fun t : ℝ =>
      Real.sqrt (∫ x : ℝ≥0, ‖phase t x - 1‖ ^ 2 ∂μ) / Real.sqrt |t|)
      (𝓝[≠] 0) (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp
    («FIN-EXT025-C01-spectral-square» hm)
  simpa only [Function.comp_def, Real.sqrt_zero, integral_div, Real.sqrt_div' _ (abs_nonneg _)] using h

end QuantumNLS.Ext025B3FormSpectral

#print axioms QuantumNLS.Ext025B3FormSpectral.phase_norm

#print axioms QuantumNLS.Ext025B3FormSpectral.phase_sub_bound

#print axioms QuantumNLS.Ext025B3FormSpectral.square_bound

#print axioms QuantumNLS.Ext025B3FormSpectral.quotient_bound

#print axioms QuantumNLS.Ext025B3FormSpectral.quotient_limit

#print axioms QuantumNLS.Ext025B3FormSpectral.square_limit

#print axioms QuantumNLS.Ext025B3FormSpectral.«FIN-EXT025-C01-spectral-derivative»

#print axioms QuantumNLS.Ext025B3FormSpectral.«FIN-EXT025-C01-spectral-square»

#print axioms QuantumNLS.Ext025B3FormSpectral.spectral_hasDerivAt
#print axioms QuantumNLS.Ext025B3FormSpectral.spectral_sqrt_ratio

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025B3FormSpectral." then
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
  Lean.logInfo m!"Ext025B3FormSpectral audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
