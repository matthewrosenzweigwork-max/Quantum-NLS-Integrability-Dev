import Mathlib

/-!
R-275B7656 support, positive-remainder argument (positive_moments.tex:78-106).
This module proves the GP-11 application, including finiteness rather than presupposing it.
The real scalar remainder limits are explicit inputs to this SUPPORT theorem. They are not
asserted to follow from the physical Riccati theorem in this module, and no physical theorem
or reality of all classical charges is claimed here.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace QuantumNLS.SmoothScalarMomentsPositive

/-- The positive finite geometric remainder at heights y = n+1. -/
def kernel (m n : ℕ) (t : ℝ) : ℝ :=
  t ^ (2 * m) / (1 + t ^ 2 / ((n : ℝ) + 1) ^ 2)

lemma kernel_nonneg (m n : ℕ) (t : ℝ) : 0 ≤ kernel m n t := by
  unfold kernel
  exact div_nonneg (pow_nonneg (sq_nonneg t) m |>.trans_eq (pow_mul t 2 m).symm)
    (by positivity)

lemma kernel_continuous (m n : ℕ) : Continuous (kernel m n) := by
  unfold kernel
  exact (continuous_id.pow _).div
    (continuous_const.add ((continuous_id.pow 2).div_const _))
    (fun t => ne_of_gt (by positivity))

lemma kernel_mono (m : ℕ) (t : ℝ) : Monotone (fun n => kernel m n t) := by
  intro n k hnk
  have ha : 0 < (n : ℝ) + 1 := by positivity
  have hb : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnk 1
  have hd : 1 + t ^ 2 / ((k : ℝ) + 1) ^ 2 ≤ 1 + t ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    gcongr
  exact div_le_div_of_nonneg_left (by rw [pow_mul]; positivity : 0 ≤ t ^ (2 * m))
    (by positivity) hd

lemma kernel_tendsto (m : ℕ) (t : ℝ) :
    Tendsto (fun n => kernel m n t) atTop (𝓝 (t ^ (2 * m))) := by
  have hi : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hq : Tendsto (fun n : ℕ => t ^ 2 / ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      (tendsto_const_nhds (x := t ^ 2)).mul (hi.pow 2)
  have h := (tendsto_const_nhds (x := t ^ (2 * m))).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add hq) (by norm_num : (1 : ℝ) + 0 ≠ 0)
  convert h using 1 <;> simp [kernel, Pi.div_def]

lemma kernel_zero_le_one (n : ℕ) (t : ℝ) : kernel 0 n t ≤ 1 := by
  unfold kernel
  simp only [Nat.mul_zero, pow_zero]
  exact (div_le_one (by positivity)).2 (le_add_of_nonneg_right (by positivity))

lemma kernel_step (m n : ℕ) (t : ℝ) :
    kernel (m + 1) n t = ((n : ℝ) + 1) ^ 2 * (t ^ (2 * m) - kernel m n t) := by
  have hy : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hd : (1 + t ^ 2 / ((n : ℝ) + 1) ^ 2) ≠ 0 := by positivity
  unfold kernel
  rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
  field_simp
  ring

lemma kernel_step_bound (m n : ℕ) (t : ℝ) :
    kernel (m + 1) n t ≤ ((n : ℝ) + 1) ^ 2 * t ^ (2 * m) := by
  rw [kernel_step]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (kernel_nonneg _ _ _)) (sq_nonneg _)

/-- GP-11 with a finite limiting integral. No integrability of F is assumed. -/
theorem recover_nonnegative {μ : Measure ℝ} {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {c : ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hpos : ∀ n t, 0 ≤ f n t)
    (hmono : ∀ t, Monotone (fun n => f n t))
    (hlim : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (F t)))
    (hF : AEStronglyMeasurable F μ)
    (hc : Tendsto (fun n => ∫ t, f n t ∂μ) atTop (𝓝 c)) :
    Integrable F μ ∧ ∫ t, F t ∂μ = c := by
  have hFpos : ∀ t, 0 ≤ F t := fun t => ge_of_tendsto' (hlim t) (fun n => hpos n t)
  have hMCT := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hf n).aemeasurable.ennreal_ofReal)
    (ae_of_all μ fun t n k hnk => ENNReal.ofReal_le_ofReal (hmono t hnk))
    (ae_of_all μ fun t => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim t))
  have hfinite : (∫⁻ t, ENNReal.ofReal (F t) ∂μ) = ENNReal.ofReal c := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc
    change Tendsto (fun n => ENNReal.ofReal (∫ t, f n t ∂μ)) atTop (𝓝 (ENNReal.ofReal c)) at h
    simp_rw [ofReal_integral_eq_lintegral_ofReal (hf _) (ae_of_all μ (hpos _))] at h
    exact tendsto_nhds_unique hMCT h
  have hInt : Integrable F μ :=
    (lintegral_ofReal_ne_top_iff_integrable hF (ae_of_all μ hFpos)).1
      (by rw [hfinite]; exact ENNReal.ofReal_ne_top)
  exact ⟨hInt, tendsto_nhds_unique
    (integral_tendsto_of_tendsto_of_monotone hf hInt
      (ae_of_all μ hmono) (ae_of_all μ hlim)) hc⟩

/-- Recursive form of the exact finite geometric remainders. c m denotes I_(2m+1).
For example R1=y²(c0-F), R2=y²(c1-R1). The sign alternation is essential. -/
def remainder (F : ℕ → ℝ) (c : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => F n
  | m + 1, n => ((n : ℝ) + 1) ^ 2 * (c m - remainder F c m n)

/-- Exact finite geometric identity after integration; only LOWER moments are inputs. -/
lemma kernel_integral_eq_remainder (μ : Measure ℝ) (c : ℕ → ℝ) (m n : ℕ)
    (hlower : ∀ j < m, Integrable (fun t : ℝ => t ^ (2 * j)) μ ∧
      ∫ t, t ^ (2 * j) ∂μ = c j) :
    ∫ t, kernel m n t ∂μ =
      remainder (fun n => ∫ t, kernel 0 n t ∂μ) c m n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hLow := hlower m (by omega)
    have hK : Integrable (kernel m n) μ :=
      hLow.1.mono' (kernel_continuous m n).aestronglyMeasurable
        (ae_of_all μ fun t => by
          rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg _ _ _)]
          unfold kernel
          exact div_le_self (by rw [pow_mul]; positivity) (le_add_of_nonneg_right (by positivity)))
    simp_rw [kernel_step]
    rw [integral_const_mul, integral_sub hLow.1 hK, hLow.2,
      ih (fun j hj => hlower j (by omega))]
    rfl

/-- All even moments from the finite limits of the positive remainders. This is
an analytic support theorem; its input limits must be derived from REAL coefficients
of the physical Cauchy expansion before applying it to R-275B7656. -/
theorem even_moments_of_remainder_limits (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℕ → ℝ)
    (hlimits : ∀ m, Tendsto
      (remainder (fun n => ∫ t, kernel 0 n t ∂μ) c m) atTop (𝓝 (c m))) :
    ∀ m, Integrable (fun t : ℝ => t ^ (2 * m)) μ ∧
      ∫ t, t ^ (2 * m) ∂μ = c m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hInt : ∀ n, Integrable (kernel m n) μ := by
      intro n
      cases m with
      | zero =>
        exact (integrable_const (1 : ℝ)).mono'
          (kernel_continuous 0 n).aestronglyMeasurable
          (ae_of_all μ fun t => by
            rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg 0 n t)]
            exact kernel_zero_le_one n t)
      | succ k =>
        exact ((ih k (by omega)).1.const_mul (((n : ℝ) + 1) ^ 2)).mono'
          (kernel_continuous (k + 1) n).aestronglyMeasurable
          (ae_of_all μ fun t => by
            rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg _ _ _)]
            exact kernel_step_bound k n t)
    exact recover_nonnegative hInt (kernel_nonneg m) (kernel_mono m)
      (kernel_tendsto m) (by fun_prop)
      ((hlimits m).congr (fun n =>
        (kernel_integral_eq_remainder μ c m n ih).symm))

/-- Interpolation: every absolute integer moment follows from the even moments.
The scalar values c are never assumed to be moments. -/
theorem all_absolute_moments_of_remainder_limits (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℕ → ℝ)
    (hlimits : ∀ m, Tendsto
      (remainder (fun n => ∫ t, kernel 0 n t ∂μ) c m) atTop (𝓝 (c m))) :
    ∀ r : ℕ, Integrable (fun t : ℝ => |t| ^ r) μ := by
  intro r
  have heven := (even_moments_of_remainder_limits μ c hlimits r).1
  have hnorm : Integrable (fun t : ℝ => ‖t‖ ^ (2 * r)) μ := by
    exact heven.congr (ae_of_all μ fun t => by
      change t ^ (2 * r) = ‖t‖ ^ (2 * r)
      rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by rw [pow_mul]; positivity)])
  simpa only [Real.norm_eq_abs] using
    integrable_norm_pow_of_le (μ := μ) (f := fun t : ℝ => t)
      (by fun_prop) (show r ≤ 2 * r by omega) hnorm

#print axioms recover_nonnegative
#print axioms kernel_integral_eq_remainder
#print axioms even_moments_of_remainder_limits
#print axioms all_absolute_moments_of_remainder_limits
end QuantumNLS.SmoothScalarMomentsPositive

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.SmoothScalarMomentsPositive." ||
        n.toString.startsWith "_private.QuantumNLS.SmoothScalarMomentsPositive." then
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
