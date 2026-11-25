import Mathlib.Analysis.Normed.Group.Constructions

/-!
Exact coercion identity for the nonnegative scalar used as the source-Pi
matrix multiplication Lipschitz constant.
-/

set_option autoImplicit false

open scoped NNReal

namespace NlsGge.SpectralFoundations

theorem sourcePi_nnreal_lipschitzConstant_coe (C : ℝ) (hC : 0 ≤ C) :
    ((⟨2 * C, mul_nonneg (by norm_num) hC⟩ : ℝ≥0) : ℝ) = 2 * C := rfl

end NlsGge.SpectralFoundations
