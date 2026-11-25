import QuantumNLS.SmoothScalarMomentsPositive

/-! R-275B7656 analytic coefficient identification after positive moment recovery.
The complex scalar remainders are the finite resolvent remainders; no moment value is
assumed. No physical Riccati statement is postulated or reconstructed in this module. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace QuantumNLS.SmoothScalarMomentsCauchy

def height (n : ℕ) : ℂ := ((n : ℝ) + 1) * Complex.I

def resolvent (r n : ℕ) (t : ℝ) : ℂ :=
  height n * (t : ℂ) ^ r / (height n - t)

lemma height_im (n : ℕ) : (height n).im = (n : ℝ) + 1 := by simp [height]

lemma height_norm (n : ℕ) : ‖height n‖ = (n : ℝ) + 1 := by
  have h : ‖height n‖ ^ 2 = ((n : ℝ) + 1) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [height, Complex.normSq_apply, pow_two]
  nlinarith [norm_nonneg (height n), (show (0 : ℝ) < (n : ℝ) + 1 by positivity)]

lemma denominator_ne_zero (n : ℕ) (t : ℝ) : height n - t ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, height_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
  have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  linarith

lemma denominator_bound (n : ℕ) (t : ℝ) : ‖height n‖ ≤ ‖height n - t‖ := by
  rw [height_norm]
  have h := Complex.im_le_norm (height n - t)
  simpa only [Complex.sub_im, height_im, Complex.ofReal_im, sub_zero] using h

lemma resolvent_norm (r n : ℕ) (t : ℝ) : ‖resolvent r n t‖ ≤ |t| ^ r := by
  rw [resolvent, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    mul_comm, mul_div_assoc]
  apply mul_le_of_le_one_right (by positivity)
  exact (div_le_one (norm_pos_iff.mpr (denominator_ne_zero n t))).2 (denominator_bound n t)

lemma resolvent_tendsto (r : ℕ) (t : ℝ) :
    Tendsto (fun n => resolvent r n t) atTop (𝓝 ((t : ℂ) ^ r)) := by
  have hi : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hiC : Tendsto (fun n : ℕ => (height n)⁻¹) atTop (𝓝 0) := by
    simpa [height, mul_inv_rev, Complex.ofReal_inv] using
      (tendsto_const_nhds (x := Complex.I⁻¹)).mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hi)
  have hq := (tendsto_const_nhds (x := (t : ℂ))).mul hiC
  have hden := (tendsto_const_nhds (x := (1 : ℂ))).sub hq
  have hh := (tendsto_const_nhds (x := (t : ℂ) ^ r)).div hden (by norm_num : (1 : ℂ) - t * 0 ≠ 0)
  convert hh using 1
  · funext n
    have hz : height n ≠ 0 := by
      intro h
      have h1 := congrArg Complex.im h
      simp only [height_im, Complex.zero_im] at h1
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      linarith
    dsimp [resolvent]
    field_simp
  · simp

lemma resolvent_measurable (r n : ℕ) : AEStronglyMeasurable (resolvent r n) (volume : Measure ℝ) := by
  have hc : Continuous (resolvent r n) := by
    unfold resolvent
    exact (continuous_const.mul (Complex.continuous_ofReal.pow r)).div
      (continuous_const.sub Complex.continuous_ofReal) (denominator_ne_zero n)
  exact hc.aestronglyMeasurable

lemma integrable_resolvent (μ : Measure ℝ) (r n : ℕ)
    (h : Integrable (fun t : ℝ => |t| ^ r) μ) : Integrable (resolvent r n) μ := by
  have hc : Continuous (resolvent r n) := by
    unfold resolvent
    exact (continuous_const.mul (Complex.continuous_ofReal.pow r)).div
      (continuous_const.sub Complex.continuous_ofReal) (denominator_ne_zero n)
  exact h.mono' hc.aestronglyMeasurable (ae_of_all μ (resolvent_norm r n))

lemma integrable_power (μ : Measure ℝ) (r : ℕ)
    (h : Integrable (fun t : ℝ => |t| ^ r) μ) : Integrable (fun t : ℝ => (t : ℂ) ^ r) μ := by
  exact h.mono' (by fun_prop) (ae_of_all μ fun t => by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs])

/-- The finite resolvent identity. -/
lemma resolvent_step (r n : ℕ) (t : ℝ) :
    resolvent (r + 1) n t = height n * (resolvent r n t - (t : ℂ) ^ r) := by
  unfold resolvent
  rw [pow_succ]
  field_simp [denominator_ne_zero n t]
  ring

lemma resolvent_integral_tendsto (μ : Measure ℝ) (r : ℕ)
    (h : Integrable (fun t : ℝ => |t| ^ r) μ) :
    Tendsto (fun n => ∫ t, resolvent r n t ∂μ) atTop (𝓝 (∫ t, (t : ℂ) ^ r ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ => |t| ^ r)
  · intro n
    exact (integrable_resolvent μ r n h).aestronglyMeasurable
  · exact h
  · intro n
    exact ae_of_all μ (resolvent_norm r n)
  · exact ae_of_all μ (resolvent_tendsto r)

/-- Complex recursive scalar coefficient remainder; c r denotes I_(r+1). -/
def remainder (G : ℕ → ℂ) (c : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, n => height n * G n
  | r + 1, n => height n * (remainder G c r n - c r)

/-- Once absolute moments have been recovered by positivity, the finite Cauchy
remainders identify EVERY coefficient, including the odd moments. -/
theorem moments_of_remainder_limits (μ : Measure ℝ)
    (c : ℕ → ℂ) (habs : ∀ r : ℕ, Integrable (fun t : ℝ => |t| ^ r) μ)
    (hlimits : ∀ r, Tendsto
      (remainder (fun n => ∫ t : ℝ, (height n - t)⁻¹ ∂μ) c r) atTop (𝓝 (c r))) :
    ∀ r : ℕ, ∫ t : ℝ, (t : ℂ) ^ r ∂μ = c r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    have hid : ∀ j ≤ r, ∀ n,
        ∫ t, resolvent j n t ∂μ =
          remainder (fun n => ∫ t : ℝ, (height n - t)⁻¹ ∂μ) c j n := by
      intro j hj n
      induction j with
      | zero =>
        simp only [resolvent, pow_zero, mul_one, remainder, div_eq_mul_inv]
        exact integral_const_mul _ _
      | succ j ihj =>
        simp_rw [resolvent_step]
        rw [integral_const_mul,
          integral_sub (integrable_resolvent μ j n (habs j)) (integrable_power μ j (habs j)),
          ihj (by omega), ih j (by omega)]
        rfl
    have h := resolvent_integral_tendsto μ r (habs r)
    exact tendsto_nhds_unique h ((hlimits r).congr (fun n => (hid r le_rfl n).symm))

/-- Analytic part of the smooth-moments argument in ONE theorem: real even
positive-remainder limits imply absolute moments; the complex resolvent remainder
limits identify every moment. These scalar limits are hypotheses, not asserted
physical consequences of the still-missing Riccati prerequisite. -/
theorem all_scalar_moments (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℕ → ℝ)
    (hpositive : ∀ m, Tendsto
      (QuantumNLS.SmoothScalarMomentsPositive.remainder
        (fun n => ∫ t, QuantumNLS.SmoothScalarMomentsPositive.kernel 0 n t ∂μ)
        (fun m => c (2 * m)) m) atTop (𝓝 (c (2 * m))))
    (hcomplex : ∀ r, Tendsto
      (remainder (fun n => ∫ t : ℝ, (height n - t)⁻¹ ∂μ)
        (fun r => (c r : ℂ)) r) atTop (𝓝 (c r : ℂ))) :
    ∀ r : ℕ, Integrable (fun t : ℝ => |t| ^ r) μ ∧
      ∫ t : ℝ, (t : ℂ) ^ r ∂μ = (c r : ℂ) := by
  have habs := QuantumNLS.SmoothScalarMomentsPositive.all_absolute_moments_of_remainder_limits
    μ (fun m => c (2 * m)) hpositive
  exact fun r => ⟨habs r, moments_of_remainder_limits μ (fun r => (c r : ℂ)) habs hcomplex r⟩

#print axioms all_scalar_moments
#print axioms resolvent_integral_tendsto
#print axioms moments_of_remainder_limits
end QuantumNLS.SmoothScalarMomentsCauchy

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.SmoothScalarMomentsCauchy." ||
        n.toString.startsWith "_private.QuantumNLS.SmoothScalarMomentsCauchy." then
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
