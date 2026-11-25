import Mathlib

/- MCGAPSCALAR PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target
   NlsGge/ThirdConsultation/M/CentralGapScalar.lean, namespace NlsGge.ThirdConsultation.MCentralGapS. Mathlib-only scalar
   support for Pro round 16 Q2 zero_gap_small_H1 / central_gap_radius (no packet increment). -/
set_option autoImplicit false
namespace NlsGge.ThirdConsultation.MCentralGapS

/-- A point of `[lo, hi]` is bounded by any common bound of the endpoints. -/
theorem abs_le_of_mem_Icc {lo hi x R : ℝ} (hx : x ∈ Set.Icc lo hi) (hlo : |lo| ≤ R) (hhi : |hi| ≤ R) :
    |x| ≤ R :=
  abs_le.mpr ⟨by linarith [neg_abs_le lo, hx.1], by linarith [le_abs_self hi, hx.2]⟩

theorem sqrt_two_lt : Real.sqrt 2 < 3 / 2 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `Q ≤ 1/4`: `Q² + √2 Q ≤ 7/16 < 1/2`. -/
theorem small_bound {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ : Q ≤ 1 / 4) : Q ^ 2 + Real.sqrt 2 * Q ≤ 1 / 2 := by
  have h1 : Real.sqrt 2 * Q ≤ 3 / 2 * (1 / 4) :=
    mul_le_mul sqrt_two_lt.le hQ hQ0 (by norm_num)
  have h2 : Q ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
  linarith

/-- `Q ≥ 1/4`: `Q² + √2 Q ≤ (1 + 4√2) Q² < 8π Q²`. -/
theorem large_bound {Q : ℝ} (hQ : 1 / 4 ≤ Q) : Q ^ 2 + Real.sqrt 2 * Q ≤ 8 * Real.pi * Q ^ 2 := by
  have hQ0 : 0 ≤ Q := by linarith
  have h4 : Q ≤ 4 * Q ^ 2 := by nlinarith
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h1 : Real.sqrt 2 * Q ≤ 3 / 2 * (4 * Q ^ 2) :=
    mul_le_mul sqrt_two_lt.le h4 hQ0 (by norm_num)
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hq2 : 0 ≤ Q ^ 2 := sq_nonneg Q
  nlinarith

/-- Low labels: `(8Q² - 1/2) π ≤ 8π Q²`. -/
theorem low_bound (Q : ℝ) : (8 * Q ^ 2 - 1 / 2) * Real.pi ≤ 8 * Real.pi * Q ^ 2 := by
  nlinarith [Real.pi_pos]

end NlsGge.ThirdConsultation.MCentralGapS
