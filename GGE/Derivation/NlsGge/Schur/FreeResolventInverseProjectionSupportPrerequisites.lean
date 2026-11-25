import Mathlib.Algebra.Ring.Basic
import NlsGge.Analysis.H1Multiplication

set_option autoImplicit false

namespace NlsGge.Schur

/-- If `A` is supported on both sides by an idempotent projection `Q`, then
`1 - A` commutes with `Q`; its two-sided inverse therefore commutes with `Q`
as well. This is the algebraic step used to restrict the concrete Neumann
inverse to the complementary range. -/
theorem inverse_commutes_with_bilateral_projection_support
    {R : Type*} [Ring R] (Q A S : R)
    (hAQ : A * Q = A) (hQA : Q * A = A)
    (hSr : S * (1 - A) = 1) (hSl : (1 - A) * S = 1) :
    Q * S = S * Q := by
  have hcomm : Q * (1 - A) = (1 - A) * Q := by
    calc
      Q * (1 - A) = Q - Q * A := by rw [mul_sub, mul_one]
      _ = Q - A := by rw [hQA]
      _ = (1 - A) * Q := by rw [sub_mul, one_mul, hAQ]
  calc
    Q * S = (S * (1 - A)) * Q * S := by rw [hSr]; simp
    _ = S * ((1 - A) * Q) * S := by simp only [mul_assoc]
    _ = S * (Q * (1 - A)) * S := by rw [hcomm]
    _ = (S * Q) * ((1 - A) * S) := by simp only [mul_assoc]
    _ = S * Q := by rw [hSl]; simp

/-- The concrete H¹ multiplier constant and every radius `R ≥ 1` give the
nonnegative Neumann-series bound without an opaque positivity search. -/
theorem physicalH1MultiplierConstant_radius_nonneg
    (R : ℝ) (hR : 1 ≤ R) :
    0 ≤ 2 * NlsGge.Analysis.physicalH1MultiplierConstant * R := by
  apply mul_nonneg
  · exact mul_nonneg (by norm_num) NlsGge.Analysis.physicalH1MultiplierConstant_pos.le
  · exact le_trans (by norm_num) hR

end NlsGge.Schur
