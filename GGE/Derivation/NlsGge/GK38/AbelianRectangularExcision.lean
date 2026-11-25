import NlsGge.GK38.ActionContourGeometry
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Small SOURCE-ONLY prefix for the book14.11 finite-hole Cauchy step.
Actual oriented edge integrals and earned original-family horizontal geometry.
No contour-excision/final-period identity is assumed or asserted here.
Targets+English were recorded before proof authoring. UNCOMPILED. -/
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

def p6RectBoundary38 (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, f ((x : ℂ)+(c : ℂ)*Complex.I)) -
    (∫ x : ℝ in a..b, f ((x : ℂ)+(d : ℂ)*Complex.I)) +
    Complex.I*(∫ y : ℝ in c..d, f ((b : ℂ)+(y : ℂ)*Complex.I)) -
    Complex.I*(∫ y : ℝ in c..d, f ((a : ℂ)+(y : ℂ)*Complex.I))

theorem p6RectBoundary_horizontal_split38 (f : ℂ → ℂ) (a t b c d : ℝ)
    (hc0 : IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+(c : ℂ)*Complex.I)) volume a t)
    (hc1 : IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+(c : ℂ)*Complex.I)) volume t b)
    (hd0 : IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+(d : ℂ)*Complex.I)) volume a t)
    (hd1 : IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+(d : ℂ)*Complex.I)) volume t b) :
    p6RectBoundary38 f a b c d =
      p6RectBoundary38 f a t c d + p6RectBoundary38 f t b c d := by
  unfold p6RectBoundary38
  rw [← intervalIntegral.integral_add_adjacent_intervals hc0 hc1,
    ← intervalIntegral.integral_add_adjacent_intervals hd0 hd1]
  abel

theorem p6RectBoundary_vertical_split38 (f : ℂ → ℂ) (a b c t d : ℝ)
    (ha0 : IntervalIntegrable (fun y : ℝ => f ((a : ℂ)+(y : ℂ)*Complex.I)) volume c t)
    (ha1 : IntervalIntegrable (fun y : ℝ => f ((a : ℂ)+(y : ℂ)*Complex.I)) volume t d)
    (hb0 : IntervalIntegrable (fun y : ℝ => f ((b : ℂ)+(y : ℂ)*Complex.I)) volume c t)
    (hb1 : IntervalIntegrable (fun y : ℝ => f ((b : ℂ)+(y : ℂ)*Complex.I)) volume t d) :
    p6RectBoundary38 f a b c d =
      p6RectBoundary38 f a b c t + p6RectBoundary38 f a b t d := by
  unfold p6RectBoundary38
  rw [← intervalIntegral.integral_add_adjacent_intervals ha0 ha1,
    ← intervalIntegral.integral_add_adjacent_intervals hb0 hb1]
  ring

theorem p6RectBoundary_zero_of_differentiableOn38 (f : ℂ → ℂ) (a b c d : ℝ)
    (hf : DifferentiableOn ℂ f ((Set.uIcc a b) ×ℂ (Set.uIcc c d))) :
    p6RectBoundary38 f a b c d = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ)+(c : ℂ)*Complex.I) ((b : ℂ)+(d : ℂ)*Complex.I)
    (by simpa using hf)
  simpa [p6RectBoundary38, smul_eq_mul] using h

theorem p6Isolating_horizontal_separation38 (φ : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (m n : ℤ) (hmn : m < n) :
    (C m).re+R m < (C n).re-R n := by
  obtain ⟨c,N,hgeom,_⟩ := hfam
  have hsep := isolating_geometry_closure_separated38 C R c N hgeom m n (ne_of_lt hmn)
  have hc := hgeom.2.1 hmn
  rw [dist_eq_norm, realType_norm_sub_real38 _ _ (hgeom.1 m).2 (hgeom.1 n).2,
    abs_of_neg (sub_neg.mpr hc)] at hsep
  linarith

end
end NlsGge.GK38
