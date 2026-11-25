import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace NlsGge.Schur

/-- `exp(-4d) q² ≤ I` from `2q/(1+2d) ≤ g` and `g²/4 ≤ I`. -/
theorem gapAction_exp_comparison38V1 (d q g I : ℝ) (hd0 : 0 ≤ d) (hq : 0 ≤ q)
    (hg : 2 * q / (1 + 2 * d) ≤ g) (hI : g ^ 2 / 4 ≤ I) :
    Real.exp (-4 * d) * q ^ 2 ≤ I := by
  have hpos : 0 < 1 + 2 * d := by linarith
  have hq2 : 2 * q ≤ g * (1 + 2 * d) := by
    rwa [div_le_iff₀ hpos] at hg
  have hq0 : 0 ≤ 2 * q := by linarith
  have hsq : (2 * q) ^ 2 ≤ (g * (1 + 2 * d)) ^ 2 := pow_le_pow_left₀ hq0 hq2 2
  have hq3 : q ^ 2 ≤ (1 + 2 * d) ^ 2 * I := by nlinarith [sq_nonneg (1 + 2 * d)]
  have hexp1 : 1 + 2 * d ≤ Real.exp (2 * d) := by
    have := Real.add_one_le_exp (2 * d); linarith
  have hexp : (1 + 2 * d) ^ 2 ≤ Real.exp (4 * d) := by
    have h := pow_le_pow_left₀ hpos.le hexp1 2
    have : Real.exp (2 * d) ^ 2 = Real.exp (4 * d) := by
      rw [← Real.exp_nat_mul]; norm_num; ring_nf
    linarith
  have hI0 : 0 ≤ I := le_trans (by positivity) hI
  have hE : 0 < Real.exp (-4 * d) := Real.exp_pos _
  have hmul : Real.exp (-4 * d) * Real.exp (4 * d) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-4 * d) * q ^ 2 ≤ Real.exp (-4 * d) * ((1 + 2 * d) ^ 2 * I) :=
        mul_le_mul_of_nonneg_left hq3 hE.le
    _ ≤ Real.exp (-4 * d) * (Real.exp (4 * d) * I) := by
        apply mul_le_mul_of_nonneg_left _ hE.le
        exact mul_le_mul_of_nonneg_right hexp hI0
    _ = I := by rw [← mul_assoc, hmul, one_mul]

end NlsGge.Schur
