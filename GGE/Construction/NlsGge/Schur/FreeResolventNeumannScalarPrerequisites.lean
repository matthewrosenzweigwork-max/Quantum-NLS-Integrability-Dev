import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

namespace NlsGge.Schur

/-- Scalar inverse bound used after the squared Neumann term is at most one
half. -/
theorem real_inv_one_sub_le_two {r : ℝ} (hr : r ≤ 1 / 2) :
    (1 - r)⁻¹ ≤ 2 := by
  have hden : 1 / 2 ≤ 1 - r := by linarith
  calc
    (1 - r)⁻¹ = 1 / (1 - r) := by rw [one_div]
    _ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hden
    _ = 2 := by norm_num

/-- Scalar addition-order bridge for the continuous-operator Neumann bound. -/
theorem norm_one_add_le_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Nontrivial E] (A : E →L[ℂ] E) (B : ℝ) (hA : ‖A‖ ≤ B) :
    ‖1 + A‖ ≤ 1 + B := by
  calc
    ‖1 + A‖ ≤ ‖(1 : E →L[ℂ] E)‖ + ‖A‖ := norm_add_le _ _
    _ = 1 + ‖A‖ := by rw [norm_one]
    _ ≤ 1 + B := add_le_add_right hA 1

end NlsGge.Schur
