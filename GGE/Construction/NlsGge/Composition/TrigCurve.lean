import Mathlib

/-!
# W03: the trigonometric curve `t ↦ ∑_{n ∈ S} e_n(t) v_n` is real analytic

Source: `paper/v2.tex`, lines 1464-1466 (the trigonometric polynomial `p`, analytic in `θ`).

* `NlsGge.Composition.trigCurve S v t = ∑ n ∈ S, fourier n t • v n` for a complex Banach
  space `X` viewed as a real space;
* `trigCurve_hasFPowerSeries` : an everywhere convergent real power series expansion around any
  `t₀`, with coefficient bounds `‖P m‖ ≤ (∑ ‖v n‖) (2π N)^m / m!` when `|n| ≤ N` on `S`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NlsGge.Composition

open scoped Nat

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The trigonometric polynomial `t ↦ ∑_{n ∈ S} e^{2π i n t} v n` with values in `X`. -/
def trigCurve (S : Finset ℤ) (v : ℤ → X) (t : ℝ) : X :=
  ∑ n ∈ S, fourier n (t : AddCircle (1 : ℝ)) • v n

theorem trigCurve_eq_circle (S : Finset ℤ) (v : ℤ → X) (t : ℝ) :
    trigCurve S v t =
      (fun θ : AddCircle (1 : ℝ) => ∑ n ∈ S, fourier n θ • v n) (t : AddCircle (1 : ℝ)) := rfl

theorem trigCurve_periodic (S : Finset ℤ) (v : ℤ → X) : Function.Periodic (trigCurve S v) 1 := by
  intro t
  unfold trigCurve
  have : ((t + 1 : ℝ) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_add]
    simp
  rw [this]

theorem trigCurve_continuous (S : Finset ℤ) (v : ℤ → X) : Continuous (trigCurve S v) := by
  unfold trigCurve
  refine continuous_finsetSum _ fun n _ => ?_
  exact ((fourier n).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))).smul continuous_const

/-- Shift formula for the characters. -/
theorem fourier_coe_add (n : ℤ) (t s : ℝ) :
    fourier n ((t + s : ℝ) : AddCircle (1 : ℝ)) =
      fourier n (t : AddCircle (1 : ℝ)) *
        Complex.exp (2 * Real.pi * Complex.I * n * s) := by
  rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Coefficient `m` of the expansion around `t₀`, as an element of `X`. -/
def trigCoeff (S : Finset ℤ) (v : ℤ → X) (t₀ : ℝ) (m : ℕ) : X :=
  ∑ n ∈ S, (fourier n (t₀ : AddCircle (1 : ℝ)) *
    ((2 * Real.pi * Complex.I * n) ^ m / (m ! : ℂ))) • v n

theorem trigCoeff_norm_le (S : Finset ℤ) (v : ℤ → X) (t₀ : ℝ) (N : ℝ)
    (hN : ∀ n ∈ S, |(n : ℝ)| ≤ N) (m : ℕ) :
    ‖trigCoeff S v t₀ m‖ ≤ (∑ n ∈ S, ‖v n‖) * (2 * Real.pi * N) ^ m / m ! := by
  unfold trigCoeff
  calc ‖∑ n ∈ S, (fourier n (t₀ : AddCircle (1 : ℝ)) *
        ((2 * Real.pi * Complex.I * n) ^ m / (m ! : ℂ))) • v n‖
      ≤ ∑ n ∈ S, ‖(fourier n (t₀ : AddCircle (1 : ℝ)) *
        ((2 * Real.pi * Complex.I * n) ^ m / (m ! : ℂ))) • v n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ‖v n‖ * ((2 * Real.pi * N) ^ m / m !) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have h1 : ‖fourier n (t₀ : AddCircle (1 : ℝ))‖ = 1 := by
          rw [fourier_apply]; exact Circle.norm_coe _
        have h2 : ‖(2 * Real.pi * Complex.I * n : ℂ)‖ = 2 * Real.pi * |(n : ℝ)| := by
          simp [Complex.norm_I, abs_of_pos Real.pi_pos]
        have h3 : ‖((m ! : ℕ) : ℂ)‖ = (m ! : ℝ) := by simp
        rw [norm_smul, norm_mul, norm_div, norm_pow, h1, h2, h3, one_mul, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left (hN n hn) (by positivity)) m
    _ = (∑ n ∈ S, ‖v n‖) * (2 * Real.pi * N) ^ m / m ! := by
        rw [← Finset.sum_mul, mul_div_assoc]

/-- The power series `∑ m, y^m • trigCoeff S v t₀ m`, as a formal multilinear series. -/
def trigSeries (S : Finset ℤ) (v : ℤ → X) (t₀ : ℝ) : FormalMultilinearSeries ℝ ℝ X :=
  fun m => ContinuousMultilinearMap.mkPiRing ℝ (Fin m) (trigCoeff S v t₀ m)

theorem trigSeries_apply (S : Finset ℤ) (v : ℤ → X) (t₀ : ℝ) (m : ℕ) (y : ℝ) :
    trigSeries S v t₀ m (fun _ => y) = y ^ m • trigCoeff S v t₀ m := by
  simp [trigSeries, ContinuousMultilinearMap.mkPiRing_apply]

theorem trigSeries_norm_le (S : Finset ℤ) (v : ℤ → X) (t₀ : ℝ) (N : ℝ)
    (hN : ∀ n ∈ S, |(n : ℝ)| ≤ N) (m : ℕ) :
    ‖trigSeries S v t₀ m‖ ≤ (∑ n ∈ S, ‖v n‖) * (2 * Real.pi * N) ^ m / m ! := by
  unfold trigSeries
  rw [ContinuousMultilinearMap.norm_mkPiRing]
  exact trigCoeff_norm_le S v t₀ N hN m

theorem trigSeries_hasSum (S : Finset ℤ) (v : ℤ → X) (t₀ y : ℝ) :
    HasSum (fun m : ℕ => trigSeries S v t₀ m (fun _ => y)) (trigCurve S v (t₀ + y)) := by
  simp_rw [trigSeries_apply, trigCoeff, Finset.smul_sum]
  unfold trigCurve
  refine hasSum_sum fun n _ => ?_
  have hs := NormedSpace.expSeries_div_hasSum_exp (2 * Real.pi * Complex.I * n * y : ℂ)
  rw [← Complex.exp_eq_exp_ℂ] at hs
  have h := (hs.mul_left (fourier n (t₀ : AddCircle (1 : ℝ)))).smul_const (v n)
  rw [← fourier_coe_add] at h
  convert h using 2 with m
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  rw [mul_pow]
  ring

/-- Real-analytic expansion of the trigonometric curve around any point. -/
theorem trigCurve_hasFPowerSeries (S : Finset ℤ) (v : ℤ → X) (t₀ : ℝ) (N : ℝ) (hN0 : 0 ≤ N)
    (hN : ∀ n ∈ S, |(n : ℝ)| ≤ N) :
    ∃ P : FormalMultilinearSeries ℝ ℝ X, HasFPowerSeriesOnBall (trigCurve S v) P t₀ ⊤ ∧
      ∀ m, ‖P m‖ ≤ (∑ n ∈ S, ‖v n‖) * (2 * Real.pi * N) ^ m / m.factorial := by
  refine ⟨trigSeries S v t₀, ⟨?_, ENNReal.zero_lt_top, fun _ => trigSeries_hasSum S v t₀ _⟩,
    trigSeries_norm_le S v t₀ N hN⟩
  refine ENNReal.le_of_forall_nnreal_lt fun r _ => ?_
  refine (trigSeries S v t₀).le_radius_of_bound
    ((∑ n ∈ S, ‖v n‖) * Real.exp (2 * Real.pi * N * r)) fun m => ?_
  calc ‖trigSeries S v t₀ m‖ * (r : ℝ) ^ m
      ≤ (∑ n ∈ S, ‖v n‖) * (2 * Real.pi * N) ^ m / m ! * (r : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right (trigSeries_norm_le S v t₀ N hN m) (by positivity)
    _ = (∑ n ∈ S, ‖v n‖) * ((2 * Real.pi * N * r) ^ m / m !) := by
        rw [mul_pow]; ring
    _ ≤ (∑ n ∈ S, ‖v n‖) * Real.exp (2 * Real.pi * N * r) :=
        mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp _ (by positivity) m)
          (Finset.sum_nonneg fun _ _ => norm_nonneg _)

end NlsGge.Composition
