import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Elementary inverse geometry for GK Lemma 15.1

This discharges the numerical conversion in source node `GK15.1.inverseGeometry`
(`references/gk/gk.txt`, lines 5012–5016). For arbitrary complex endpoints `a`, `b`
and terminal point `μ`, the nearest endpoint distance is at most the distance to
the midpoint plus half the gap. The sharp square-root factor is consequently at
most the gap plus the distance to the midpoint, with universal constant one.
There are no spectral assumptions, including no nondegeneracy assumptions.

The proof uses only the pinned Mathlib (commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Apache-2.0): the norm triangle
inequality, `Complex.norm_div`, `Complex.norm_two`, `Real.sqrt_mul` and
`Real.sqrt_le_left`. No project provider or draft theorem is imported.
-/

set_option autoImplicit false

namespace NlsGge.GK38

/-- Triangle inequality from the midpoint bounds the nearest endpoint distance.
All three points are arbitrary complex numbers. -/
theorem min_norm_sub_le_midpoint_distance_add_half_gap38 (a b μ : ℂ) :
    min ‖μ - a‖ ‖μ - b‖ ≤ ‖μ - (a + b) / 2‖ + ‖a - b‖ / 2 := by
  have hmid : (a + b) / 2 - a = (b - a) / 2 := by ring
  calc
    min ‖μ - a‖ ‖μ - b‖ ≤ ‖μ - a‖ := min_le_left _ _
    _ ≤ ‖μ - (a + b) / 2‖ + ‖(a + b) / 2 - a‖ :=
      norm_sub_le_norm_sub_add_norm_sub μ ((a + b) / 2) a
    _ = ‖μ - (a + b) / 2‖ + ‖a - b‖ / 2 := by
      rw [hmid, Complex.norm_div, Complex.norm_two, norm_sub_rev b a]

/-- The elementary square-root product estimate, valid also when either real
parameter vanishes. Nonnegativity is stated before using square-root identities. -/
theorem sqrt_gap_add_distance_mul_sqrt_distance_le38 {g d : ℝ}
    (hg : 0 ≤ g) (hd : 0 ≤ d) :
    Real.sqrt (g + d) * Real.sqrt d ≤ d + g / 2 := by
  rw [← Real.sqrt_mul (add_nonneg hg hd)]
  apply (Real.sqrt_le_left (add_nonneg hd (div_nonneg hg (by norm_num)))).mpr
  nlinarith only [sq_nonneg g]

/-- GK15.1's sharp endpoint factor is bounded by gap plus midpoint distance,
with universal constant `1`. The binders are arbitrary complex endpoints and a
terminal point; there are no hypotheses and no exceptional endpoint cases. -/
theorem raw_beta_magnitude_inverse_geometry38 (a b μ : ℂ) :
    Real.sqrt (‖a - b‖ + min ‖μ - a‖ ‖μ - b‖) *
        Real.sqrt (min ‖μ - a‖ ‖μ - b‖) ≤
      ‖a - b‖ + ‖μ - (a + b) / 2‖ := by
  have hd : 0 ≤ min ‖μ - a‖ ‖μ - b‖ :=
    le_min (norm_nonneg _) (norm_nonneg _)
  calc
    Real.sqrt (‖a - b‖ + min ‖μ - a‖ ‖μ - b‖) *
          Real.sqrt (min ‖μ - a‖ ‖μ - b‖) ≤
        min ‖μ - a‖ ‖μ - b‖ + ‖a - b‖ / 2 :=
      sqrt_gap_add_distance_mul_sqrt_distance_le38 (norm_nonneg _) hd
    _ ≤ ‖a - b‖ + ‖μ - (a + b) / 2‖ := by
      linarith only [min_norm_sub_le_midpoint_distance_add_half_gap38 a b μ]

end NlsGge.GK38
