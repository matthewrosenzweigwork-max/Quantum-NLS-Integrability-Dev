import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB2DuhamelKernel

/-! # Track B, step B2: the fixed-cutoff Duhamel output is a Schwartz function

For a time-side Schwartz cutoff `η`, a frequency `λ` and a Schwartz forcing mode `g`, the
fixed-cutoff Duhamel output `t ↦ η(t) ∫₀ᵗ e^{-iλ(t-r)} g(r) dr` is again a Schwartz function
(`duhOut η λ g`). Proof: the unimodular phase `e^{iat}` has temperate growth (all derivatives
`(ia)ⁿ e^{iat}`), the primitive `P(t) = ∫₀ᵗ e^{iλr} g(r) dr` has temperate growth (bounded by
`∫|g|`, derivative `e^{iλt} g(t)` of temperate growth), and the output is `η · (e^{-iλ·} P)`,
a Schwartz function times a function of temperate growth (`smulLeftCLM`).
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory SchwartzMap
open scoped ENNReal

/-- The unimodular phase `t ↦ e^{iat}`. -/
def ph (a t : ℝ) : ℂ := Complex.exp (↑(a * t) * Complex.I)

theorem norm_ph (a t : ℝ) : ‖ph a t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_ph (a : ℝ) : Continuous (ph a) := by
  unfold ph
  fun_prop

theorem hasDerivAt_ph (a t : ℝ) : HasDerivAt (ph a) (a * Complex.I * ph a t) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((a * s : ℝ) : ℂ)) (a : ℂ) t := by
    have := ((hasDerivAt_id t).const_mul a).ofReal_comp
    simpa using this
  have h2 := (h1.mul_const Complex.I).cexp
  unfold ph
  convert h2 using 1
  ring

theorem iteratedDeriv_ph (a : ℝ) (n : ℕ) :
    iteratedDeriv n (ph a) = fun t => (a * Complex.I) ^ n * ph a t := by
  induction n with
  | zero => funext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [((hasDerivAt_ph a t).const_mul ((a * Complex.I) ^ n)).deriv]
    ring

theorem hasTemperateGrowth_ph (a : ℝ) : (ph a).HasTemperateGrowth := by
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => ?_, fun n => ⟨0, |a| ^ n, fun t => ?_⟩⟩
  · rw [iteratedDeriv_ph]
    exact fun t => (hasDerivAt_ph a t).differentiableAt.const_mul _
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_ph, norm_mul, norm_ph, norm_pow,
      norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
    simp

/-- The modulated primitive `P(t) = ∫₀ᵗ e^{iλr} g(r) dr`. -/
def primS (lam : ℝ) (g : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ := ∫ r in (0 : ℝ)..t, ph lam r * g r

theorem continuous_phg (lam : ℝ) (g : 𝓢(ℝ, ℂ)) : Continuous fun r => ph lam r * g r :=
  (continuous_ph lam).mul g.continuous

theorem hasDerivAt_primS (lam : ℝ) (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    HasDerivAt (primS lam g) (ph lam t * g t) t :=
  ((continuous_phg lam g).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem integrable_phg (lam : ℝ) (g : 𝓢(ℝ, ℂ)) : Integrable fun r => ph lam r * g r := by
  refine g.integrable.bdd_mul (c := 1) (continuous_ph lam).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun r => (norm_ph lam r).le

theorem norm_primS_le (lam : ℝ) (g : 𝓢(ℝ, ℂ)) (t : ℝ) : ‖primS lam g t‖ ≤ ∫ r, ‖g r‖ := by
  unfold primS
  refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
  calc ∫ r in Set.uIoc 0 t, ‖ph lam r * g r‖ ≤ ∫ r, ‖ph lam r * g r‖ :=
        setIntegral_le_integral (integrable_phg lam g).norm
          (Filter.Eventually.of_forall fun r => norm_nonneg _)
    _ = ∫ r, ‖g r‖ := by simp only [norm_mul, norm_ph, one_mul]

theorem hasTemperateGrowth_primS (lam : ℝ) (g : 𝓢(ℝ, ℂ)) : (primS lam g).HasTemperateGrowth := by
  have hq : (fun r => ph lam r * g r).HasTemperateGrowth :=
    (hasTemperateGrowth_ph lam).mul g.hasTemperateGrowth
  have hfd : fderiv ℝ (primS lam g) =
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip ∘ fun r => ph lam r * g r := by
    funext t
    rw [(hasDerivAt_primS lam g t).hasFDerivAt.fderiv]
    ext
    simp
  refine Function.HasTemperateGrowth.of_fderiv (k := 0) (C := ∫ r, ‖g r‖) ?_
    (fun t => (hasDerivAt_primS lam g t).differentiableAt) (fun t => ?_)
  · rw [hfd]
    exact (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip.hasTemperateGrowth.comp hq
  · rw [pow_zero, mul_one]
    exact norm_primS_le lam g t

/-- The phase-shifted primitive `t ↦ e^{-iλt} ∫₀ᵗ e^{iλr} g(r) dr = ∫₀ᵗ e^{-iλ(t-r)} g(r) dr`. -/
def duhPrim (lam : ℝ) (g : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ := ph (-lam) t * primS lam g t

theorem hasTemperateGrowth_duhPrim (lam : ℝ) (g : 𝓢(ℝ, ℂ)) :
    (duhPrim lam g).HasTemperateGrowth :=
  (hasTemperateGrowth_ph (-lam)).mul (hasTemperateGrowth_primS lam g)

theorem duhPrim_eq (lam : ℝ) (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    duhPrim lam g t = ∫ r in (0 : ℝ)..t, ph (-lam) (t - r) * g r := by
  unfold duhPrim primS
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [ph]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The fixed-cutoff Duhamel output** `η(t) ∫₀ᵗ e^{-iλ(t-r)} g(r) dr` as a Schwartz function. -/
def duhOut (η : 𝓢(ℝ, ℂ)) (lam : ℝ) (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (duhPrim lam g) η

theorem duhOut_apply (η : 𝓢(ℝ, ℂ)) (lam : ℝ) (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    duhOut η lam g t = η t * ∫ r in (0 : ℝ)..t, ph (-lam) (t - r) * g r := by
  rw [duhOut, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_duhPrim lam g),
    smul_eq_mul, duhPrim_eq, mul_comm]

end LiebLiniger.FixedPeriod.ALLS.PdeB
