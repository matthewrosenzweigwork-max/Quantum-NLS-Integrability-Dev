import QuantumNLS.SmoothScalarMomentsMain

/-! R-275B7656: convert the ordinary finite inverse-power estimates to
recursive coefficient limits. No physical expansion is assumed in the final
physical interface; this module is the elementary analytic conversion only. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter Topology
namespace QuantumNLS.SmoothScalarMomentsAsymptotic
open QuantumNLS.SmoothScalarMomentsCauchy

def series (c : ℕ → ℂ) (M : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range M, c j * z⁻¹ ^ (j + 1)

lemma series_succ (c : ℕ → ℂ) (M : ℕ) (z : ℂ) :
    series c (M + 1) z = series c M z + c M * z⁻¹ ^ (M + 1) := by
  simp [series, Finset.sum_range_succ]

lemma height_ne_zero (n : ℕ) : height n ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [height_norm]; positivity)

lemma remainder_error (G c : ℕ → ℂ) (r n : ℕ) :
    remainder G c r n - c r = height n ^ (r + 1) * (G n - series c (r + 1) (height n)) := by
  induction r with
  | zero =>
    simp only [remainder, series, Finset.range_one, Finset.sum_singleton, pow_one,
      zero_add]
    field_simp [height_ne_zero n]
  | succ r ih =>
    rw [remainder, ih]
    rw [series_succ c (r + 1)]
    have hz : height n ^ (r + 1 + 1) * (height n)⁻¹ ^ (r + 1 + 1) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (height_ne_zero n), one_pow]
    calc height n * (height n ^ (r + 1) * (G n - series c (r + 1) (height n))) - c (r + 1)
        = height n ^ (r + 1 + 1) * (G n - series c (r + 1) (height n)) - c (r + 1) := by
            rw [pow_succ]; ring
      _ = height n ^ (r + 1 + 1) *
          (G n - (series c (r + 1) (height n) + c (r + 1) * (height n)⁻¹ ^ (r + 1 + 1))) := by
            linear_combination c (r + 1) * hz

/-- Conventional all-order inverse-power expansion, with constants depending
on order. This is an analytic helper, not a permitted physical prerequisite. -/
def Expansion (G c : ℕ → ℂ) : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∃ C R : ℝ, ∀ n : ℕ, R ≤ ‖height n‖ →
    ‖G n - series c M (height n)‖ ≤ C * (‖height n‖ ^ (M + 1))⁻¹

/-- The ordinary expansion implies every coefficient limit used by GP-11. -/
theorem limits_of_expansion {G c : ℕ → ℂ} (hexp : Expansion G c) (r : ℕ) :
    Tendsto (remainder G c r) atTop (𝓝 (c r)) := by
  obtain ⟨C, R, hb⟩ := hexp (r + 1) (by omega)
  have hy : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop, ‖remainder G c r n - c r‖ ≤ C / ((n : ℝ) + 1) := by
    filter_upwards [hy.eventually_ge_atTop R] with n hn
    rw [← height_norm] at hn
    rw [remainder_error, norm_mul, norm_pow]
    calc ‖height n‖ ^ (r + 1) * ‖G n - series c (r + 1) (height n)‖
        ≤ ‖height n‖ ^ (r + 1) * (C * (‖height n‖ ^ (r + 1 + 1))⁻¹) :=
          mul_le_mul_of_nonneg_left (hb n hn) (by positivity)
      _ = C / ((n : ℝ) + 1) := by
        rw [height_norm, pow_succ]
        have h : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        ring
  have hlim : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hy
  have hz := squeeze_zero' (Eventually.of_forall fun n => norm_nonneg (remainder G c r n - c r)) he hlim
  rw [← tendsto_zero_iff_norm_tendsto_zero] at hz
  simpa only [sub_add_cancel, zero_add] using hz.add_const (c r)

#print axioms remainder_error
#print axioms limits_of_expansion
end QuantumNLS.SmoothScalarMomentsAsymptotic

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.SmoothScalarMomentsAsymptotic." ||
        n.toString.startsWith "_private.QuantumNLS.SmoothScalarMomentsAsymptotic." then
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
