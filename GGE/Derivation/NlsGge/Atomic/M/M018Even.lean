import Mathlib
import NlsGge.Atomic.M.M014
import NlsGge.GK38.RealTypeSpectrumLevels
import NlsGge.Spectral.ActualQuasimomentumE02_38

/- M-018 EVEN-ORDER COMPARISON, PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORT (no
   packet increment). Target NlsGge/Atomic/M/M018Even.lean, namespace NlsGge.ThirdConsultation.M018E.
   From the landed M-014 gap-integral formula higherAction u n k = (2/π)∫_{λ⁻}^{λ⁺} x^(k-1) h(x) dx with h ≥ 0 and
   λ⁻ ≤ λ⁺, and |x|^(2m-1) ≤ (x^(2m-2) + x^(2m))/2: an even-order action is dominated by the two neighbouring odd
   actions.  Used to transfer uniform tails (h782 odd_higher_action_tails_of_tendsto) to even orders in M-018. -/
set_option autoImplicit false
open MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.M018E

open NlsGge.ThirdConsultation.M

theorem pow_odd_abs_le (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    |x ^ (2 * m - 1)| ≤ (x ^ (2 * m - 2) + x ^ (2 * m)) / 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have e1 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have e2 : 2 * (j + 1) - 2 = 2 * j := by omega
  have e3 : 2 * (j + 1) = 2 * j + 2 := by omega
  rw [e1, e2, e3]
  have hy : 0 ≤ x ^ (2 * j) := by rw [pow_mul]; positivity
  have h1 : |x ^ (2 * j + 1)| = x ^ (2 * j) * |x| := by
    rw [pow_succ, abs_mul, abs_of_nonneg hy]
  have h2 : |x| ≤ (1 + x ^ 2) / 2 := by
    nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
  rw [h1, show x ^ (2 * j + 2) = x ^ (2 * j) * x ^ 2 by ring]
  nlinarith [mul_le_mul_of_nonneg_left h2 hy]

theorem even_action_le (u : PhysicalL2) (n : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    |higherAction u n (2 * m)| ≤
      (higherAction u n (2 * m - 1) + higherAction u n (2 * m + 1)) / 2 := by
  obtain ⟨-, -, hi0, -, he0⟩ := higher_action_gap_integral u n (2 * m) (by omega)
  obtain ⟨-, -, hi1, -, he1⟩ := higher_action_gap_integral u n (2 * m - 1) (by omega)
  obtain ⟨-, -, hi2, -, he2⟩ := higher_action_gap_integral u n (2 * m + 1) (by omega)
  have k0 : 2 * m - 1 - 1 = 2 * m - 2 := by omega
  have k2 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [k0] at hi1 he1
  rw [k2] at hi2 he2
  rw [he0, he1, he2]
  have hab : periodicMinus u n ≤ periodicPlus u n := (gap_endpoint_levels38 u n).1
  have hh : ∀ x : ℝ, 0 ≤ spectralHeight u n x := fun x => actualGapHeightE02_38_nonneg u x
  set a := periodicMinus u n
  set b := periodicPlus u n
  have hpi : 0 < 2 / Real.pi := by positivity
  have hsum : (∫ x in a..b, x ^ (2 * m - 2) * spectralHeight u n x) +
      (∫ x in a..b, x ^ (2 * m) * spectralHeight u n x) =
      ∫ x in a..b, (x ^ (2 * m - 2) * spectralHeight u n x + x ^ (2 * m) * spectralHeight u n x) :=
    (intervalIntegral.integral_add hi1 hi2).symm
  have hle : |∫ x in a..b, x ^ (2 * m - 1) * spectralHeight u n x| ≤
      (∫ x in a..b, (x ^ (2 * m - 2) * spectralHeight u n x + x ^ (2 * m) * spectralHeight u n x)) / 2 := by
    calc |∫ x in a..b, x ^ (2 * m - 1) * spectralHeight u n x|
        ≤ ∫ x in a..b, |x ^ (2 * m - 1) * spectralHeight u n x| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ x in a..b, (x ^ (2 * m - 2) * spectralHeight u n x +
            x ^ (2 * m) * spectralHeight u n x) / 2 := by
          refine intervalIntegral.integral_mono_on hab hi0.abs ((hi1.add hi2).div_const 2) ?_
          intro x _
          rw [abs_mul, abs_of_nonneg (hh x)]
          have := mul_le_mul_of_nonneg_right (pow_odd_abs_le x m hm) (hh x)
          linarith
      _ = (∫ x in a..b, (x ^ (2 * m - 2) * spectralHeight u n x +
            x ^ (2 * m) * spectralHeight u n x)) / 2 := intervalIntegral.integral_div _ _
  rw [abs_mul, abs_of_pos hpi, ← mul_add, hsum]
  have := mul_le_mul_of_nonneg_left hle hpi.le
  linarith

end NlsGge.ThirdConsultation.M018E
