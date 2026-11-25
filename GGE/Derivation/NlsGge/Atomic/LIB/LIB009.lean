import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false

open Metric

namespace NlsGge.Atomic.LIB

noncomputable section

/-- Banach-valued Cauchy formula in the fixed Mathlib circle convention.

`circleIntegral` is parameterized by `circleMap c R θ` with `θ` increasing from
`0` to `2π`; this is the positive (counterclockwise) orientation. The scalar
factor is the reciprocal of `2πi`, and the complex scalar multiplies the
Banach-valued integrand on the left, as in Mathlib's source theorem. The
interior condition on `w` entails `0 < R`.
-/
theorem banach_cauchy_formula {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {c w : ℂ} {R : ℝ} {f : ℂ → E}
    (h : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
        circleIntegral (fun z : ℂ => (z - w)⁻¹ • f z) c R = f w := by
  exact DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul h hw

end
end NlsGge.Atomic.LIB
