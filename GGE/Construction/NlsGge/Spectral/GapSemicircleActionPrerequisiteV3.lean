import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
This file proves only the real-variable semicircle calculation and its
conditional action consequence.  It does not construct the Zakharov--Shabat
monodromy, quasimomentum, spectral gaps, or the paper's gap-height function.
In particular, the pointwise representation hypothesis below remains an E02 /
NEW-E01 prerequisite and is not asserted for any concrete potential here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace NlsGge.SpectralFoundations

/-- The semicircle profile on the interval with endpoints `a` and `b`. -/
def gapSemicircle (a b x : ℝ) : ℝ := Real.sqrt ((x - a) * (b - x))

/-- Exact area under the semicircle profile, including the degenerate interval. -/
theorem integral_gapSemicircle (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, gapSemicircle a b x) = (Real.pi / 8) * (b - a) ^ 2 := by
  by_cases hab' : a = b
  · subst b
    simp [gapSemicircle]
  let r : ℝ := (b - a) / 2
  let m : ℝ := (a + b) / 2
  have hablt : a < b := lt_of_le_of_ne hab hab'
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (sub_pos.mpr hablt) (by norm_num)
  have hr0 : 0 ≤ r := le_of_lt hr
  have hleft : -r + m = a := by
    dsimp [r, m]
    ring
  have hright : r + m = b := by
    dsimp [r, m]
    ring
  have hchange :
      r * (∫ t in (-1 : ℝ)..1, gapSemicircle a b (r * t + m)) =
        ∫ x in a..b, gapSemicircle a b x := by
    simpa only [smul_eq_mul, mul_neg_one, mul_one, hleft, hright] using
      (intervalIntegral.smul_integral_comp_mul_add
        (f := gapSemicircle a b) (a := (-1 : ℝ)) (b := (1 : ℝ)) r m)
  have hprofile : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      gapSemicircle a b (r * t + m) = r * Real.sqrt (1 - t ^ 2) := by
    intro t ht
    have hrad :
        (r * t + m - a) * (b - (r * t + m)) = r ^ 2 * (1 - t ^ 2) := by
      dsimp [r, m]
      ring
    rw [gapSemicircle, hrad, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hr0]
  calc
    (∫ x in a..b, gapSemicircle a b x) =
        r * (∫ t in (-1 : ℝ)..1, gapSemicircle a b (r * t + m)) := hchange.symm
    _ = r * (∫ t in (-1 : ℝ)..1, r * Real.sqrt (1 - t ^ 2)) := by
      congr 1
      exact intervalIntegral.integral_congr (by
        intro t ht
        exact hprofile t (by
          simpa only [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht))
    _ = r * (r * (∫ t in (-1 : ℝ)..1, Real.sqrt (1 - t ^ 2))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (Real.pi / 8) * (b - a) ^ 2 := by
      rw [integral_sqrt_one_sub_sq]
      dsimp [r]
      ring

/--
Conditional form of the universal action estimate.  The assumptions `hrep`
and `hY` are precisely a local gap-height representation and its nonnegative
correction; E02/NEW-E01 must realize them for the concrete spectral data before
this lemma can be used to discharge the paper claim.
-/
theorem gapAction_lowerBound_of_gapHeight
    (a b : ℝ) (hab : a ≤ b) (v Y : ℝ → ℝ)
    (hv : IntervalIntegrable v volume a b)
    (hsemi : IntervalIntegrable (gapSemicircle a b) volume a b)
    (hrep : ∀ x ∈ Set.Icc a b,
      v x = gapSemicircle a b x * (1 + Y x))
    (hY : ∀ x ∈ Set.Icc a b, 0 ≤ Y x) :
    (b - a) ^ 2 / 4 ≤ (2 / Real.pi) * (∫ x in a..b, v x) := by
  have hsemi_nonneg : ∀ x ∈ Set.Icc a b, 0 ≤ gapSemicircle a b x := by
    intro x hx
    apply Real.sqrt_nonneg
  have hpoint : ∀ x ∈ Set.Icc a b, gapSemicircle a b x ≤ v x := by
    intro x hx
    rw [hrep x hx]
    have hs := hsemi_nonneg x hx
    have hy := hY x hx
    nlinarith [mul_nonneg hs hy]
  have hint := intervalIntegral.integral_mono_on hab hsemi hv hpoint
  have harea := integral_gapSemicircle a b hab
  have hpi : 0 < Real.pi := Real.pi_pos
  have hscale : (2 / Real.pi) * ((Real.pi / 8) * (b - a) ^ 2) =
      (b - a) ^ 2 / 4 := by
    field_simp [ne_of_gt hpi]
    ring
  calc
    (b - a) ^ 2 / 4 = (2 / Real.pi) *
        (∫ x in a..b, gapSemicircle a b x) := by rw [harea, hscale]
    _ ≤ (2 / Real.pi) * (∫ x in a..b, v x) :=
      mul_le_mul_of_nonneg_left hint (by positivity)

end NlsGge.SpectralFoundations
