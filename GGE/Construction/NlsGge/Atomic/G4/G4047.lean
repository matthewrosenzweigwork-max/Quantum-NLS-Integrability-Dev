import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# GK-16.4: logarithmic small-gap bound

The elementary real logarithm estimate is uniform down to arbitrarily small
positive `a`; the only division hypothesis is `0 < a`.
-/

namespace NlsGge.Atomic.G4

/-- For `a > 0` and `b ≥ 0`, the logarithmic term is bounded after
multiplication by `a`, without a positive lower bound on `a`. -/
theorem mul_log_one_add_div_le {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    a * Real.log (1 + b / a) ≤ b := by
  have harg : 0 < 1 + b / a := by
    have hdiv : 0 ≤ b / a := div_nonneg hb ha.le
    linarith
  have hlog := Real.log_le_sub_one_of_pos harg
  have hquot : (1 + b / a) - 1 = b / a := by ring
  rw [hquot] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog ha.le
  calc
    a * Real.log (1 + b / a) ≤ a * (b / a) := hmul
    _ = b := by field_simp [ne_of_gt ha]

/-- The affine version used in the GK logarithmic primitive estimate. -/
theorem mul_add_log_one_add_div_le {a b C : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    a * (C + Real.log (1 + b / a)) ≤ C * a + b := by
  calc
    a * (C + Real.log (1 + b / a)) = C * a + a * Real.log (1 + b / a) := by ring
    _ ≤ C * a + b := by linarith [mul_log_one_add_div_le ha hb]

end NlsGge.Atomic.G4
