import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

open scoped ContDiff

/-!
# Negativity of the quartic `Q₆` functional on a periodic cusp

Source: `paper/v2.tex`, proof of `C:prop:negative`.  The recorded tactic-level variation of the
manuscript strategy replaces the cut-off cusp `η(x)(x²+ε²)^{3/8}` by the periodic cusp
`(sin²(πx)+ε²)^{3/8}`.  With `s = sin²πx + ε²`, `g = sin²πx`, `t = g/s` one has the exact identity
`14 f² f''² - 7 f'⁴ = π⁴ s^{-1/2} G(g,t)` with `G(0,1) = -441/256`; `G` is bounded by an
explicit linear comparison, the resulting integral is bounded above by
`π⁴(-(441/256)·A + 49·B + 49·C)` where `A ≥ (1/5)log(1/(2ε))`, `B ≤ 1`, `C ≤ 2`, and `ε = e^{-500}`
gives a negative value.
-/

namespace NlsGge.HierarchyRiccati.Core

/-- The quartic part of the real `Q₆` density, `14 f² (f'')² - 7 (f')⁴`, integrated over the
unit period. -/
noncomputable def q6QuarticF38 (f : ℝ → ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, (14 * (f x) ^ 2 * (iteratedDeriv 2 f x) ^ 2 - 7 * (deriv f x) ^ 4)

/-- The periodic cusp `(sin²(πx) + ε²)^{3/8}`. -/
noncomputable def periodicCusp38 (ε : ℝ) (x : ℝ) : ℝ :=
  (Real.sin (Real.pi * x) ^ 2 + ε ^ 2) ^ ((3:ℝ) / 8)

/-- Base `sin²(πx) + ε²`. -/
noncomputable def cuspS38 (ε x : ℝ) : ℝ := Real.sin (Real.pi * x) ^ 2 + ε ^ 2

/-- First derivative of the base. -/
noncomputable def cuspS1_38 (x : ℝ) : ℝ := 2 * Real.pi * Real.sin (Real.pi * x) * Real.cos (Real.pi * x)

/-- Second derivative of the base. -/
noncomputable def cuspS2_38 (x : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * (Real.cos (Real.pi * x) ^ 2 - Real.sin (Real.pi * x) ^ 2)

theorem cuspS38_pos (ε : ℝ) (hε : 0 < ε) (x : ℝ) : 0 < cuspS38 ε x := by
  unfold cuspS38; positivity

theorem hasDerivAt_cuspS38 (ε x : ℝ) : HasDerivAt (cuspS38 ε) (cuspS1_38 x) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
    simpa using (hasDerivAt_id x).const_mul Real.pi
  have h2 := (h1.sin).fun_pow 2
  have h3 := h2.add_const (ε ^ 2)
  refine h3.congr_deriv ?_
  unfold cuspS1_38
  simp
  ring

theorem hasDerivAt_cuspS1_38 (x : ℝ) : HasDerivAt cuspS1_38 (cuspS2_38 x) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
    simpa using (hasDerivAt_id x).const_mul Real.pi
  have h2 := ((h1.sin).const_mul (2 * Real.pi)).fun_mul h1.cos
  have h3 : cuspS1_38 = fun y => 2 * Real.pi * Real.sin (Real.pi * y) * Real.cos (Real.pi * y) := rfl
  rw [h3]
  refine h2.congr_deriv ?_
  unfold cuspS2_38; ring

theorem hasDerivAt_periodicCusp38 (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (periodicCusp38 ε) (cuspS1_38 x * ((3:ℝ) / 8) * cuspS38 ε x ^ ((3:ℝ) / 8 - 1)) x :=
  (hasDerivAt_cuspS38 ε x).rpow_const (Or.inl (cuspS38_pos ε hε x).ne')

theorem deriv_periodicCusp38 (ε : ℝ) (hε : 0 < ε) :
    deriv (periodicCusp38 ε) =
      fun y => ((3:ℝ) / 8) * cuspS38 ε y ^ (-(5:ℝ) / 8) * cuspS1_38 y := by
  funext y
  rw [(hasDerivAt_periodicCusp38 ε hε y).deriv]
  have : (3:ℝ) / 8 - 1 = -(5:ℝ) / 8 := by norm_num
  rw [this]; ring

theorem iteratedDeriv_two_periodicCusp38 (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    iteratedDeriv 2 (periodicCusp38 ε) x =
      ((3:ℝ) / 8) * (cuspS38 ε x ^ (-(5:ℝ) / 8) * cuspS2_38 x +
        (-(5:ℝ) / 8) * cuspS38 ε x ^ (-(5:ℝ) / 8 - 1) * cuspS1_38 x * cuspS1_38 x) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_periodicCusp38 ε hε]
  have h1 := ((hasDerivAt_cuspS38 ε x).rpow_const (p := -(5:ℝ) / 8)
    (Or.inl (cuspS38_pos ε hε x).ne')).const_mul ((3:ℝ) / 8)
  have h2 := h1.fun_mul (hasDerivAt_cuspS1_38 x)
  rw [h2.deriv]
  ring

theorem periodicCusp38_contDiff (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (periodicCusp38 ε) := by
  have h : ContDiff ℝ ∞ (cuspS38 ε) := by
    unfold cuspS38; fun_prop
  exact h.rpow_const_of_ne (fun x => (cuspS38_pos ε hε x).ne')

theorem periodicCusp38_periodic (ε : ℝ) : Function.Periodic (periodicCusp38 ε) 1 := by
  intro x
  unfold periodicCusp38
  have : Real.sin (Real.pi * (x + 1)) = - Real.sin (Real.pi * x) := by
    rw [mul_add, mul_one, Real.sin_add_pi]
  rw [this]; simp


/-- The bracket polynomial `G(g,t)`; at `(g,t) = (0,1)` it equals `-441/256`. -/
noncomputable def cuspG38 (g t : ℝ) : ℝ :=
  63 / 8 * ((1 - 2 * g) - 5 / 4 * (1 - g) * t) ^ 2 - 567 / 256 * (1 - g) ^ 2 * t ^ 2

theorem cuspS38_rpow_four (S : ℝ) (hS : 0 < S) :
    (S ^ ((3:ℝ) / 8)) ^ 4 = S * Real.sqrt S := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hS.le, Real.sqrt_eq_rpow]
  have : (3:ℝ) / 8 * ((4:ℕ):ℝ) = 1 + 1 / 2 := by norm_num
  rw [this, Real.rpow_add hS, Real.rpow_one]

theorem cuspS38_rpow_neg_five (S : ℝ) (hS : 0 < S) :
    S ^ (-(5:ℝ) / 8) = S ^ ((3:ℝ) / 8) / S := by
  have : -(5:ℝ) / 8 = (3:ℝ) / 8 - 1 := by norm_num
  rw [this, Real.rpow_sub_one hS.ne']

theorem cuspS38_rpow_neg_thirteen (S : ℝ) (hS : 0 < S) :
    S ^ (-(5:ℝ) / 8 - 1) = S ^ ((3:ℝ) / 8) / S / S := by
  rw [Real.rpow_sub_one hS.ne', cuspS38_rpow_neg_five S hS]

theorem cusp_algebra38 (c S r g P S1 S2 : ℝ) (hS : 0 < S) (hr : 0 < r) (hrS : r ^ 2 = S)
    (hc : c ^ 4 = S * r) (hS1 : S1 ^ 2 = 4 * P ^ 2 * g * (1 - g))
    (hS2 : S2 = 2 * P ^ 2 * (1 - 2 * g)) :
    14 * c ^ 2 * (3 / 8 * (c / S * S2 + -5 / 8 * (c / S / S) * S1 * S1)) ^ 2
        - 7 * (3 / 8 * (c / S) * S1) ^ 4
      = P ^ 4 * r⁻¹ * cuspG38 g (g / S) := by
  have hSne : S ≠ 0 := hS.ne'
  have hrne : r ≠ 0 := hr.ne'
  have e1 : 14 * c ^ 2 * (3 / 8 * (c / S * S2 + -5 / 8 * (c / S / S) * S1 * S1)) ^ 2
        - 7 * (3 / 8 * (c / S) * S1) ^ 4
      = c ^ 4 * (14 * (3 / 8) ^ 2 * (S2 / S - 5 / 8 * (S1 ^ 2) / S ^ 2) ^ 2
          - 7 * (3 / 8) ^ 4 * (S1 ^ 2) ^ 2 / S ^ 4) := by
    field_simp
    ring
  rw [e1, hc, hS1, hS2]
  unfold cuspG38
  have hg : S ≠ 0 := hSne
  rw [← hrS]
  field_simp
  ring


/-- The quartic integrand of the periodic cusp, in closed form. -/
noncomputable def cuspDensity38 (ε x : ℝ) : ℝ :=
  14 * (periodicCusp38 ε x) ^ 2 * (iteratedDeriv 2 (periodicCusp38 ε) x) ^ 2
    - 7 * (deriv (periodicCusp38 ε) x) ^ 4

theorem cuspDensity38_eq (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    cuspDensity38 ε x =
      Real.pi ^ 4 * (Real.sqrt (cuspS38 ε x))⁻¹ *
        cuspG38 (Real.sin (Real.pi * x) ^ 2) (Real.sin (Real.pi * x) ^ 2 / cuspS38 ε x) := by
  have hS := cuspS38_pos ε hε x
  unfold cuspDensity38
  rw [iteratedDeriv_two_periodicCusp38 ε hε x, deriv_periodicCusp38 ε hε]
  beta_reduce
  rw [cuspS38_rpow_neg_thirteen _ hS, cuspS38_rpow_neg_five _ hS]
  have hf : periodicCusp38 ε x = cuspS38 ε x ^ ((3:ℝ) / 8) := rfl
  rw [hf]
  refine cusp_algebra38 _ _ (Real.sqrt (cuspS38 ε x)) _ Real.pi _ _ hS
    (Real.sqrt_pos.2 hS) (Real.sq_sqrt hS.le) (cuspS38_rpow_four _ hS) ?_ ?_
  · unfold cuspS1_38
    have := Real.sin_sq_add_cos_sq (Real.pi * x)
    have hc : Real.cos (Real.pi * x) ^ 2 = 1 - Real.sin (Real.pi * x) ^ 2 := by linarith
    calc (2 * Real.pi * Real.sin (Real.pi * x) * Real.cos (Real.pi * x)) ^ 2
        = 4 * Real.pi ^ 2 * Real.sin (Real.pi * x) ^ 2 * Real.cos (Real.pi * x) ^ 2 := by ring
      _ = _ := by rw [hc]
  · unfold cuspS2_38
    have := Real.sin_sq_add_cos_sq (Real.pi * x)
    have hc : Real.cos (Real.pi * x) ^ 2 = 1 - Real.sin (Real.pi * x) ^ 2 := by linarith
    rw [hc]; ring


theorem cuspG38_bound (g u : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    cuspG38 g (1 - u) ≤ -(441 / 256) + 49 * (g + u) := by
  have e : cuspG38 g (1 - u) = -(441 / 256) + (2583 / 256 * (g ^ 2 * u ^ 2) + 2457 / 128 * (g ^ 2 * u)
      + 567 / 256 * g ^ 2 - 2583 / 128 * (g * u ^ 2) - 1197 / 64 * (g * u) + 945 / 128 * g
      + 2583 / 256 * u ^ 2 - 63 / 128 * u) := by
    unfold cuspG38; ring
  rw [e]
  have h1 : g ^ 2 * u ^ 2 ≤ g := by
    have : g ^ 2 * u ^ 2 ≤ g ^ 2 * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    nlinarith
  have h2 : g ^ 2 * u ≤ g := by
    have : g ^ 2 * u ≤ g ^ 2 * 1 := mul_le_mul_of_nonneg_left hu1 (by positivity)
    nlinarith
  have h3 : g ^ 2 ≤ g := by nlinarith
  have h4 : u ^ 2 ≤ u := by nlinarith
  have h5 : 0 ≤ g * u ^ 2 := by positivity
  have h6 : 0 ≤ g * u := by positivity
  linarith


/-- The upper bound for the cusp density, in terms of explicit elementary functions. -/
noncomputable def cuspBound38 (ε x : ℝ) : ℝ :=
  Real.pi ^ 4 * (-(441 / 256) * (Real.sqrt (cuspS38 ε x))⁻¹
    + 49 * (ε ^ 2 / (cuspS38 ε x * Real.sqrt (cuspS38 ε x)))
    + 49 * Real.sqrt (cuspS38 ε x))

theorem cuspDensity38_le (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    cuspDensity38 ε x ≤ cuspBound38 ε x := by
  rw [cuspDensity38_eq ε hε x]
  have hS := cuspS38_pos ε hε x
  unfold cuspBound38
  set S := cuspS38 ε x with hSdef
  set g := Real.sin (Real.pi * x) ^ 2 with hg
  set r := Real.sqrt S with hr
  have hrpos : 0 < r := Real.sqrt_pos.2 hS
  have hrr : r * r = S := Real.mul_self_sqrt hS.le
  have hSg : S = g + ε ^ 2 := rfl
  have hg0 : 0 ≤ g := by positivity
  have hg1 : g ≤ 1 := by
    have := Real.sin_sq_le_one (Real.pi * x)
    exact this
  have hu : g / S = 1 - ε ^ 2 / S := by
    field_simp
    linarith
  have hu0 : 0 ≤ ε ^ 2 / S := by positivity
  have hu1 : ε ^ 2 / S ≤ 1 := by
    rw [div_le_one hS]; rw [hSg]; linarith
  rw [hu]
  have hG := cuspG38_bound g (ε ^ 2 / S) hg0 hg1 hu0 hu1
  have hpos : 0 ≤ Real.pi ^ 4 * r⁻¹ := by positivity
  have h1 : r⁻¹ * g ≤ r := by
    rw [inv_mul_le_iff₀ hrpos]
    nlinarith
  have h2 : r⁻¹ * (ε ^ 2 / S) = ε ^ 2 / (S * r) := by
    field_simp
  calc Real.pi ^ 4 * r⁻¹ * cuspG38 g (1 - ε ^ 2 / S)
      ≤ Real.pi ^ 4 * r⁻¹ * (-(441 / 256) + 49 * (g + ε ^ 2 / S)) :=
        mul_le_mul_of_nonneg_left hG hpos
    _ = Real.pi ^ 4 * (-(441 / 256) * r⁻¹ + 49 * (r⁻¹ * g) + 49 * (r⁻¹ * (ε ^ 2 / S))) := by ring
    _ ≤ Real.pi ^ 4 * (-(441 / 256) * r⁻¹ + 49 * (ε ^ 2 / (S * r)) + 49 * r) := by
        rw [h2]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith


theorem cuspS38_continuous (ε : ℝ) : Continuous (cuspS38 ε) := by
  unfold cuspS38; fun_prop

theorem cuspSqrtInv38_continuous (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun x => (Real.sqrt (cuspS38 ε x))⁻¹) := by
  refine Continuous.inv₀ ((cuspS38_continuous ε).sqrt) (fun x => ?_)
  exact (Real.sqrt_pos.2 (cuspS38_pos ε hε x)).ne'

theorem cuspSqrt38_continuous (ε : ℝ) : Continuous (fun x => Real.sqrt (cuspS38 ε x)) :=
  (cuspS38_continuous ε).sqrt

theorem cuspB38_continuous (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun x => ε ^ 2 / (cuspS38 ε x * Real.sqrt (cuspS38 ε x))) := by
  refine continuous_const.div ((cuspS38_continuous ε).mul (cuspSqrt38_continuous ε)) (fun x => ?_)
  exact (mul_pos (cuspS38_pos ε hε x) (Real.sqrt_pos.2 (cuspS38_pos ε hε x))).ne'

theorem cuspDensity38_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (cuspDensity38 ε) := by
  have h := periodicCusp38_contDiff ε hε
  have h0 : Continuous (periodicCusp38 ε) := h.continuous
  have h1 : Continuous (deriv (periodicCusp38 ε)) := h.continuous_deriv (by simp)
  have h2 : Continuous (iteratedDeriv 2 (periodicCusp38 ε)) :=
    h.continuous_iteratedDeriv 2 (by simp)
  unfold cuspDensity38
  fun_prop

theorem cuspBound38_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (cuspBound38 ε) := by
  have h1 := cuspSqrtInv38_continuous ε hε
  have h2 := cuspB38_continuous ε hε
  have h3 := cuspSqrt38_continuous ε
  unfold cuspBound38
  fun_prop

theorem q6QuarticF38_cusp_le (ε : ℝ) (hε : 0 < ε) :
    q6QuarticF38 (periodicCusp38 ε) ≤
      Real.pi ^ 4 * (-(441 / 256) * (∫ x in (0:ℝ)..1, (Real.sqrt (cuspS38 ε x))⁻¹)
        + 49 * (∫ x in (0:ℝ)..1, ε ^ 2 / (cuspS38 ε x * Real.sqrt (cuspS38 ε x)))
        + 49 * (∫ x in (0:ℝ)..1, Real.sqrt (cuspS38 ε x))) := by
  have e1 : q6QuarticF38 (periodicCusp38 ε) = ∫ x in (0:ℝ)..1, cuspDensity38 ε x := rfl
  rw [e1]
  have hle : (∫ x in (0:ℝ)..1, cuspDensity38 ε x) ≤ ∫ x in (0:ℝ)..1, cuspBound38 ε x :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by norm_num)
      ((cuspDensity38_continuous ε hε).intervalIntegrable _ _)
      ((cuspBound38_continuous ε hε).intervalIntegrable _ _)
      (fun x _ => cuspDensity38_le ε hε x)
  refine hle.trans (le_of_eq ?_)
  have iA := (cuspSqrtInv38_continuous ε hε).intervalIntegrable (μ := MeasureTheory.volume) (0:ℝ) 1
  have iB := (cuspB38_continuous ε hε).intervalIntegrable (μ := MeasureTheory.volume) (0:ℝ) 1
  have iC := (cuspSqrt38_continuous ε).intervalIntegrable (μ := MeasureTheory.volume) (0:ℝ) 1
  unfold cuspBound38
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (iA.const_mul _ |>.add (iB.const_mul _)) (iC.const_mul _),
    intervalIntegral.integral_add (iA.const_mul _) (iB.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]


theorem cuspC38_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x in (0:ℝ)..1, Real.sqrt (cuspS38 ε x)) ≤ 2 := by
  have h : (∫ x in (0:ℝ)..1, Real.sqrt (cuspS38 ε x)) ≤ ∫ x in (0:ℝ)..1, (2:ℝ) :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by norm_num)
      ((cuspSqrt38_continuous ε).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
      (fun x _ => by
        rw [Real.sqrt_le_left (by norm_num)]
        unfold cuspS38
        have := Real.sin_sq_le_one (Real.pi * x)
        nlinarith)
  simpa using h

theorem cuspSqrt_le_five_mul38 (ε x : ℝ) (hε : 0 < ε) (hεx : ε ≤ x) :
    Real.sqrt (cuspS38 ε x) ≤ 5 * x := by
  have hx : 0 < x := lt_of_lt_of_le hε hεx
  rw [Real.sqrt_le_left (by positivity)]
  unfold cuspS38
  have h1 : Real.sin (Real.pi * x) ^ 2 ≤ (Real.pi * x) ^ 2 := by
    by_cases h0 : Real.pi * x = 0
    · rw [h0]; simp
    · exact (Real.sin_sq_lt_sq h0).le
  have h2 : Real.pi ^ 2 ≤ 16 := by
    have := Real.pi_le_four
    have := Real.pi_pos
    nlinarith
  have h3 : ε ^ 2 ≤ x ^ 2 := by nlinarith
  have h4 : (Real.pi * x) ^ 2 ≤ 16 * x ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  nlinarith

theorem cuspA38_ge (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    (1 / 5) * Real.log ((1 / 2) / ε) ≤ ∫ x in (0:ℝ)..1, (Real.sqrt (cuspS38 ε x))⁻¹ := by
  have hεle : ε ≤ 1 / 2 := hε2.le
  have step1 : (∫ x in ε..(1 / 2 : ℝ), (1 / 5 : ℝ) * x⁻¹) ≤
      ∫ x in ε..(1 / 2 : ℝ), (Real.sqrt (cuspS38 ε x))⁻¹ := by
    refine intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hεle ?_
      ((cuspSqrtInv38_continuous ε hε).intervalIntegrable _ _) (fun x hx => ?_)
    · refine IntervalIntegrable.const_mul ?_ _
      apply intervalIntegral.intervalIntegrable_inv
      · intro x hx
        rw [Set.uIcc_of_le hεle] at hx
        exact (lt_of_lt_of_le hε hx.1).ne'
      · exact continuousOn_id
    · have hx0 : 0 < x := lt_of_lt_of_le hε hx.1
      have hsq := cuspSqrt_le_five_mul38 ε x hε hx.1
      have hpos : 0 < Real.sqrt (cuspS38 ε x) := Real.sqrt_pos.2 (cuspS38_pos ε hε x)
      have : (5 * x)⁻¹ ≤ (Real.sqrt (cuspS38 ε x))⁻¹ := inv_anti₀ hpos hsq
      calc (1 / 5 : ℝ) * x⁻¹ = (5 * x)⁻¹ := by field_simp
        _ ≤ _ := this
  have step2 : (∫ x in ε..(1 / 2 : ℝ), (Real.sqrt (cuspS38 ε x))⁻¹) ≤
      ∫ x in (0:ℝ)..1, (Real.sqrt (cuspS38 ε x))⁻¹ :=
    intervalIntegral.integral_mono_interval hε.le hεle (by norm_num)
      (Filter.Eventually.of_forall (fun x => inv_nonneg.2 (Real.sqrt_nonneg _)))
      ((cuspSqrtInv38_continuous ε hε).intervalIntegrable _ _)
  have step3 : (∫ x in ε..(1 / 2 : ℝ), (1 / 5 : ℝ) * x⁻¹) = (1 / 5) * Real.log ((1 / 2) / ε) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hε (by norm_num)]
  linarith


/-- Majorant `ε²/(4y²+ε²)^{3/2}`, the derivative of `y / √(4y²+ε²)`. -/
noncomputable def cuspRho38 (ε y : ℝ) : ℝ :=
  ε ^ 2 / ((4 * y ^ 2 + ε ^ 2) * Real.sqrt (4 * y ^ 2 + ε ^ 2))

theorem cuspRho38_hasDerivAt (ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    HasDerivAt (fun y : ℝ => y / Real.sqrt (4 * y ^ 2 + ε ^ 2)) (cuspRho38 ε y) y := by
  have hT : 0 < 4 * y ^ 2 + ε ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => 4 * y ^ 2 + ε ^ 2) (8 * y) y := by
    have := ((hasDerivAt_id y).fun_pow 2).const_mul 4 |>.add_const (ε ^ 2)
    refine this.congr_deriv ?_
    simp; ring
  have h2 := h1.sqrt hT.ne'
  have h3 := (hasDerivAt_id y).fun_div h2 (Real.sqrt_pos.2 hT).ne'
  refine h3.congr_deriv ?_
  unfold cuspRho38
  have hr := Real.sq_sqrt hT.le
  have hrpos := Real.sqrt_pos.2 hT
  simp only [id]
  generalize Real.sqrt (4 * y ^ 2 + ε ^ 2) = r at hr hrpos ⊢
  rw [← hr]
  field_simp
  linear_combination 2 * hr

theorem cuspRho38_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (cuspRho38 ε) := by
  unfold cuspRho38
  refine continuous_const.div ?_ (fun y => ?_)
  · fun_prop
  · have hT : 0 < 4 * y ^ 2 + ε ^ 2 := by positivity
    exact (mul_pos hT (Real.sqrt_pos.2 hT)).ne'

theorem cuspRho38_integral (ε : ℝ) (hε : 0 < ε) :
    (∫ y in (0:ℝ)..1, cuspRho38 ε y) ≤ 1 / 2 := by
  have h : (∫ y in (0:ℝ)..1, cuspRho38 ε y) =
      (1:ℝ) / Real.sqrt (4 * 1 ^ 2 + ε ^ 2) - 0 / Real.sqrt (4 * 0 ^ 2 + ε ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => y / Real.sqrt (4 * y ^ 2 + ε ^ 2))
      (fun y _ => cuspRho38_hasDerivAt ε hε y)
      ((cuspRho38_continuous ε hε).intervalIntegrable _ _)
  rw [h]
  have h4 : (2:ℝ) ≤ Real.sqrt (4 * 1 ^ 2 + ε ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  simp only [zero_div, sub_zero]
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

theorem cuspS38_symm (ε x : ℝ) : cuspS38 ε (1 - x) = cuspS38 ε x := by
  unfold cuspS38
  have : Real.sin (Real.pi * (1 - x)) = Real.sin (Real.pi * x) := by
    rw [mul_sub, mul_one, Real.sin_pi_sub]
  rw [this]

theorem cuspB38_le_rho_half (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    ε ^ 2 / (cuspS38 ε y * Real.sqrt (cuspS38 ε y)) ≤ cuspRho38 ε y := by
  have hS := cuspS38_pos ε hε y
  have hT : 0 < 4 * y ^ 2 + ε ^ 2 := by positivity
  have hsin : 2 * y ≤ Real.sin (Real.pi * y) := by
    have := Real.mul_le_sin (x := Real.pi * y) (by positivity)
      (by nlinarith [Real.pi_pos])
    have e : 2 / Real.pi * (Real.pi * y) = 2 * y := by
      field_simp
    linarith
  have hTS : 4 * y ^ 2 + ε ^ 2 ≤ cuspS38 ε y := by
    unfold cuspS38
    nlinarith
  unfold cuspRho38
  apply div_le_div_of_nonneg_left (by positivity) (mul_pos hT (Real.sqrt_pos.2 hT))
  exact mul_le_mul hTS (Real.sqrt_le_sqrt hTS) (Real.sqrt_nonneg _) hS.le

theorem cuspB38_le_rho (ε : ℝ) (hε : 0 < ε) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ε ^ 2 / (cuspS38 ε x * Real.sqrt (cuspS38 ε x)) ≤ cuspRho38 ε x + cuspRho38 ε (1 - x) := by
  have hr0 : ∀ y, 0 ≤ cuspRho38 ε y := fun y => by
    unfold cuspRho38
    positivity
  rcases le_total x (1 / 2) with h | h
  · have := cuspB38_le_rho_half ε hε x hx0 h
    linarith [hr0 (1 - x)]
  · have := cuspB38_le_rho_half ε hε (1 - x) (by linarith) (by linarith)
    rw [cuspS38_symm] at this
    linarith [hr0 x]

theorem cuspB38_le (ε : ℝ) (hε : 0 < ε) :
    (∫ x in (0:ℝ)..1, ε ^ 2 / (cuspS38 ε x * Real.sqrt (cuspS38 ε x))) ≤ 1 := by
  have hcont := cuspRho38_continuous ε hε
  have hrev : (∫ x in (0:ℝ)..1, cuspRho38 ε (1 - x)) = ∫ x in (0:ℝ)..1, cuspRho38 ε x := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => cuspRho38 ε x) 1]
    simp
  have h : (∫ x in (0:ℝ)..1, ε ^ 2 / (cuspS38 ε x * Real.sqrt (cuspS38 ε x))) ≤
      ∫ x in (0:ℝ)..1, (cuspRho38 ε x + cuspRho38 ε (1 - x)) :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by norm_num)
      ((cuspB38_continuous ε hε).intervalIntegrable _ _)
      ((hcont.add (hcont.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _)
      (fun x hx => cuspB38_le_rho ε hε x hx.1 hx.2)
  have i2 : IntervalIntegrable (fun x => cuspRho38 ε (1 - x)) MeasureTheory.volume 0 1 :=
    (hcont.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun x => cuspRho38 ε x) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2, hrev] at h
  have := cuspRho38_integral ε hε
  linarith


theorem exists_periodicCusp38_q6QuarticF_neg :
    ∃ ε > 0, q6QuarticF38 (periodicCusp38 ε) < 0 := by
  set ε : ℝ := Real.exp (-500) with hεdef
  have hε : 0 < ε := Real.exp_pos _
  have hε2 : ε < 1 / 2 := by
    have h1 : Real.exp (-500) < Real.exp (Real.log (1 / 2)) := by
      apply Real.exp_lt_exp.2
      have : Real.log (1 / 2) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      have h2 := Real.log_two_lt_d9
      rw [this]; linarith
    rwa [Real.exp_log (by norm_num)] at h1
  have hlog : (499 : ℝ) ≤ Real.log ((1 / 2) / ε) := by
    rw [Real.log_div (by norm_num) hε.ne', hεdef, Real.log_exp, one_div, Real.log_inv]
    have := Real.log_two_lt_d9
    linarith
  have hA := cuspA38_ge ε hε hε2
  have hB := cuspB38_le ε hε
  have hC := cuspC38_le ε hε (by linarith)
  have hF := q6QuarticF38_cusp_le ε hε
  refine ⟨ε, hε, lt_of_le_of_lt hF ?_⟩
  have hpi : 0 < Real.pi ^ 4 := by positivity
  apply mul_neg_of_pos_of_neg hpi
  linarith

end NlsGge.HierarchyRiccati.Core
