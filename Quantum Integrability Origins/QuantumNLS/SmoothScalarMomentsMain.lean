import QuantumNLS.SmoothScalarMomentsCauchy

/-! R-275B7656 analytic support: ONE real-coefficient Cauchy expansion suffices.
This module does not assert the physical Riccati-to-Cauchy binding, and its named
scalar theorem must not be reported as the requested physical R-275B7656 theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
namespace QuantumNLS.SmoothScalarMomentsMain
open QuantumNLS.SmoothScalarMomentsCauchy
namespace Pos
export QuantumNLS.SmoothScalarMomentsPositive (kernel remainder)
end Pos

lemma resolvent_zero_re (n : ℕ) (t : ℝ) :
    (QuantumNLS.SmoothScalarMomentsCauchy.resolvent 0 n t).re = Pos.kernel 0 n t := by
  have hy : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hden : t ^ 2 + ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  have hden' : ((n : ℝ) + 1) ^ 2 + t ^ 2 ≠ 0 := by positivity
  unfold QuantumNLS.SmoothScalarMomentsCauchy.resolvent Pos.kernel
  have hre : (height n).re = 0 := by simp [height]
  simp only [pow_zero, mul_one, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply, height_im, hre,
    mul_zero, zero_mul, sub_zero, zero_sub]
  field_simp
  ring

lemma kernel_integral_eq_remainder_re (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℕ → ℝ) (n : ℕ) :
    ∫ t, Pos.kernel 0 n t ∂μ =
      (remainder (fun n => ∫ t : ℝ, (height n - t)⁻¹ ∂μ) (fun r => (c r : ℂ)) 0 n).re := by
  have h0 : Integrable (fun t : ℝ => |t| ^ 0) μ := by simp
  have hr := integrable_resolvent μ 0 n h0
  calc
    _ = ∫ t, (QuantumNLS.SmoothScalarMomentsCauchy.resolvent 0 n t).re ∂μ := integral_congr_ae (ae_of_all μ fun t => (resolvent_zero_re n t).symm)
    _ = (∫ t, QuantumNLS.SmoothScalarMomentsCauchy.resolvent 0 n t ∂μ).re := integral_re hr
    _ = _ := by
      simp only [QuantumNLS.SmoothScalarMomentsCauchy.resolvent, pow_zero, mul_one, div_eq_mul_inv, remainder]
      rw [integral_const_mul]

lemma positive_remainder_eq_re (F : ℕ → ℝ) (G : ℕ → ℂ) (c : ℕ → ℝ)
    (hbase : ∀ n, F n = (height n * G n).re) (m n : ℕ) :
    Pos.remainder F (fun m => c (2 * m)) m n =
      (remainder G (fun r => (c r : ℂ)) (2 * m) n).re := by
  induction m with
  | zero => simpa only [Nat.mul_zero, Pos.remainder, remainder] using hbase n
  | succ m ih =>
    rw [Pos.remainder, ih, show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      remainder, remainder]
    have hre : (height n).re = 0 := by simp [height]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, height_im, hre,
      zero_mul, sub_zero, zero_sub, zero_add]
    ring

/-- The complete SCALAR analytic implication from one all-order real-coefficient
Cauchy expansion, stated using its recursive coefficient limits. The fixed positive
finite measure is arbitrary. The physical Riccati-to-Cauchy implication is not a premise
silently folded into a different statement: it remains separate unfinished work. -/
theorem all_moments_of_real_cauchy_expansion (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℕ → ℝ)
    (hexpansion : ∀ r, Tendsto
      (remainder (fun n => ∫ t : ℝ, (height n - t)⁻¹ ∂μ)
        (fun r => (c r : ℂ)) r) atTop (𝓝 (c r : ℂ))) :
    ∀ r : ℕ, Integrable (fun t : ℝ => |t| ^ r) μ ∧
      ∫ t : ℝ, (t : ℂ) ^ r ∂μ = (c r : ℂ) := by
  apply all_scalar_moments μ c ?_ hexpansion
  intro m
  have h := Complex.continuous_re.continuousAt.tendsto.comp (hexpansion (2 * m))
  change Tendsto (fun n => (remainder (fun n => ∫ t : ℝ, (height n - t)⁻¹ ∂μ)
    (fun r => (c r : ℂ)) (2 * m) n).re) atTop (𝓝 (c (2 * m))) at h
  exact h.congr (fun n => (positive_remainder_eq_re
    (fun n => ∫ t, Pos.kernel 0 n t ∂μ)
    (fun n => ∫ t : ℝ, (height n - t)⁻¹ ∂μ) c
    (fun n => kernel_integral_eq_remainder_re μ c n) m n).symm)

#print axioms positive_remainder_eq_re
#print axioms all_moments_of_real_cauchy_expansion
end QuantumNLS.SmoothScalarMomentsMain

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.SmoothScalarMomentsMain." ||
        n.toString.startsWith "_private.QuantumNLS.SmoothScalarMomentsMain." then
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
