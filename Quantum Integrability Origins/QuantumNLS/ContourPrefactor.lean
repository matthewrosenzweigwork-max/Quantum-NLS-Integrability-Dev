import Mathlib
import QuantumNLS.PropagationContour
import QuantumNLS.NonvanishingD

/-!
# Contour prefactor and real-part identification (scalar analogue of source `L_{N,p}`)

Owner: haiku_inventory (round 16). Source `window_reconstruction.tex` lines 206–207:
`L_{N,p} = −(1/(2πκ)) Re ∮_{Γ_N} p(z) S_N(z)/D(z) dz`.

This module is the scalar analogue: `contourFunctional κ a h f := −(1/(2πκ))·Re(rectContour a h f)`,
with `f` a supplied function (for the source, `f = p·g/D` with `g` the scalar stand-in for `S_N`).

Proved (new; the frozen `PropagationContour` is only imported):

* `re_rectContour`: the real part of the rectangle contour as four real side integrals (the vertical
  sides contribute `−Im f` through `Re(f·i) = −Im f`), under continuity of `f` on `Γ_N`;
* `abs_contourFunctional_le`: `|L| ≤ (1/(2π|κ|))·4(a+h)·M` for `‖f‖ ≤ M` on `Γ_N`;
* `contourFunctional_PROP017`: the bound for `f = p·g/D` from the PROP-017 inputs
  (`contour_bound_PROP017`).

Not claimed: operator functional calculus of `S_N`, the spectral identity between the scalar stand-in
and the source operator, polynomial class of `p`, or any PROP-017 event quantifier beyond its inputs.
-/

namespace QuantumNLS.ContourPrefactor

open MeasureTheory Set Metric intervalIntegral
open QuantumNLS.ResolventNeighborhood QuantumNLS.PropagationContour QuantumNLS.NonvanishingD

/-- Interval integral commutes with `Re` (for an interval-integrable complex integrand). -/
lemma interval_re_eq {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x).re = ∫ x in a..b, (f x).re := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have hfi : IntegrableOn f (Ioc a b) := hf.1
  have h1 := integral_re (μ := volume.restrict (Ioc a b)) hfi
  simpa using h1.symm

lemma bottom_mem {a h : ℝ} {x : ℝ} (hx : x ∈ Icc (-a) a) :
    ((x : ℂ) - (h : ℂ) * Complex.I) ∈ GammaN a h := by
  apply mem_GammaN_of_im
  · right
    simp
  · have hre : ((x : ℂ) - (h : ℂ) * Complex.I).re = x := by simp
    rw [hre, abs_le]
    constructor <;> linarith [hx.1, hx.2]

lemma top_mem {a h : ℝ} {x : ℝ} (hx : x ∈ Icc (-a) a) :
    ((x : ℂ) + (h : ℂ) * Complex.I) ∈ GammaN a h := by
  apply mem_GammaN_of_im
  · left
    simp
  · have hre : ((x : ℂ) + (h : ℂ) * Complex.I).re = x := by simp
    rw [hre, abs_le]
    constructor <;> linarith [hx.1, hx.2]

lemma right_mem {a h : ℝ} {y : ℝ} (hy : y ∈ Icc (-h) h) :
    ((a : ℂ) + (y : ℂ) * Complex.I) ∈ GammaN a h := by
  apply mem_GammaN_of_re
  · left
    simp
  · have him : ((a : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    rw [him, abs_le]
    constructor <;> linarith [hy.1, hy.2]

lemma left_mem {a h : ℝ} {y : ℝ} (hy : y ∈ Icc (-h) h) :
    (((-a : ℝ) : ℂ) + (y : ℂ) * Complex.I) ∈ GammaN a h := by
  apply mem_GammaN_of_re
  · right
    simp
  · have him : (((-a : ℝ) : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    rw [him, abs_le]
    constructor <;> linarith [hy.1, hy.2]

/-- **Real part of the rectangle contour as four real side integrals.** -/
theorem re_rectContour {a h : ℝ} {f : ℂ → ℂ} (hf : ContinuousOn f (GammaN a h))
    (ha : 0 ≤ a) (hh : 0 ≤ h) :
    (rectContour a h f).re
      = (∫ x in (-a)..a, (f ((x : ℂ) - (h : ℂ) * Complex.I)).re)
        + (∫ y in (-h)..h, -(f ((a : ℂ) + (y : ℂ) * Complex.I)).im)
        - (∫ x in (-a)..a, (f ((x : ℂ) + (h : ℂ) * Complex.I)).re)
        - (∫ y in (-h)..h, -(f (((-a : ℝ) : ℂ) + (y : ℂ) * Complex.I)).im) := by
  have hab : -a ≤ a := by linarith
  have hcd : -h ≤ h := by linarith
  have ib : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) - (h : ℂ) * Complex.I)) volume (-a) a := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    have hc : Continuous fun x : ℝ => (x : ℂ) - (h : ℂ) * Complex.I := by fun_prop
    exact ContinuousOn.comp hf hc.continuousOn (fun x hx => bottom_mem hx)
  have it : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (h : ℂ) * Complex.I)) volume (-a) a := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    have hc : Continuous fun x : ℝ => (x : ℂ) + (h : ℂ) * Complex.I := by fun_prop
    exact ContinuousOn.comp hf hc.continuousOn (fun x hx => top_mem hx)
  have ir : IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
      volume (-h) h := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hcd]
    have hc : Continuous fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I := by fun_prop
    exact (ContinuousOn.comp hf hc.continuousOn (fun y hy => right_mem hy)).mul continuousOn_const
  have il : IntervalIntegrable
      (fun y : ℝ => f (((-a : ℝ) : ℂ) + (y : ℂ) * Complex.I) * Complex.I) volume (-h) h := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hcd]
    have hc : Continuous fun y : ℝ => ((-a : ℝ) : ℂ) + (y : ℂ) * Complex.I := by fun_prop
    exact (ContinuousOn.comp hf hc.continuousOn (fun y hy => left_mem hy)).mul continuousOn_const
  unfold rectContour
  simp only [Complex.sub_re, Complex.add_re]
  rw [interval_re_eq hab ib, interval_re_eq hcd ir, interval_re_eq hab it, interval_re_eq hcd il]
  simp only [Complex.mul_I_re]

/-- The scalar contour functional `L = −(1/(2πκ))·Re ∮_{Γ_N} f` (source line 206 analogue). -/
noncomputable def contourFunctional (κ a h : ℝ) (f : ℂ → ℂ) : ℝ :=
  -(1 / (2 * Real.pi * κ)) * (rectContour a h f).re

/-- **Prefactor bound.** If `‖f‖ ≤ M` on `Γ_N` and `κ ≠ 0`, then
`|L| ≤ (1/(2π|κ|))·4(a+h)·M`. -/
theorem abs_contourFunctional_le {κ a h M : ℝ} (f : ℂ → ℂ) (hκ : κ ≠ 0) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hM0 : 0 ≤ M) (hM : ∀ z ∈ GammaN a h, ‖f z‖ ≤ M) :
    |contourFunctional κ a h f| ≤ (1 / (2 * Real.pi * |κ|)) * (4 * (a + h) * M) := by
  have hX := norm_rectContour_le f ha hh hM0 hM
  have hre := Complex.abs_re_le_norm (rectContour a h f)
  have hpre : |-(1 / (2 * Real.pi * κ))| = 1 / (2 * Real.pi * |κ|) := by
    rw [abs_neg, abs_div, abs_one, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold contourFunctional
  rw [abs_mul, hpre]
  have hpos : 0 ≤ 1 / (2 * Real.pi * |κ|) := by positivity
  calc 1 / (2 * Real.pi * |κ|) * |(rectContour a h f).re|
      ≤ 1 / (2 * Real.pi * |κ|) * (4 * (a + h) * M) :=
        mul_le_mul_of_nonneg_left (hre.trans hX) hpos

/-- **PROP-017 consumer, prefactor included.** For `f = p·g/D` with the PROP-017 inputs of
`contour_bound_PROP017`: `|L| ≤ (1/(2π|κ|))·4(a+h)·(P C/(d₀/2))`. -/
theorem contourFunctional_PROP017 {κ a h ρ d0 C P : ℝ} (g D p : ℂ → ℂ) (hκ : κ ≠ 0)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hρ : 0 ≤ ρ) (hd0 : 0 < d0) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hg : ∀ z ∈ NbhdN a h (ρ / 2), ‖g z‖ ≤ C)
    (hD : ∀ z ∈ NbhdN a h (ρ / 4), d0 / 2 ≤ ‖D z‖)
    (hp : ∀ z ∈ GammaN a h, ‖p z‖ ≤ P) :
    |contourFunctional κ a h (fun z => p z * g z / D z)|
      ≤ (1 / (2 * Real.pi * |κ|)) * (4 * (a + h) * (P * C / (d0 / 2))) := by
  have hM0 : 0 ≤ P * C / (d0 / 2) := div_nonneg (mul_nonneg hP hC) (by linarith)
  have hM : ∀ z ∈ GammaN a h, ‖p z * g z / D z‖ ≤ P * C / (d0 / 2) := by
    intro z hz
    have hzg : z ∈ NbhdN a h (ρ / 2) := GammaN_subset_NbhdN hz (by linarith)
    have hzD : z ∈ NbhdN a h (ρ / 4) := GammaN_subset_NbhdN hz (by linarith)
    have hDz := hD z hzD
    have hdpos : 0 < d0 / 2 := by linarith
    rw [norm_div, norm_mul]
    have hnum : ‖p z‖ * ‖g z‖ ≤ P * C := mul_le_mul (hp z hz) (hg z hzg) (norm_nonneg _) hP
    calc ‖p z‖ * ‖g z‖ / ‖D z‖ ≤ P * C / ‖D z‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ P * C / (d0 / 2) := div_le_div_of_nonneg_left (mul_nonneg hP hC) hdpos hDz
  exact abs_contourFunctional_le (fun z => p z * g z / D z) hκ ha hh hM0 hM

end QuantumNLS.ContourPrefactor
