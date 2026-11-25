import NlsGge.Measure.ComplexGaussian

set_option autoImplicit false

namespace NlsGge.Measure

/-- Coordinate expansion of the real exponent in the complex Gaussian shift
density. The conjugation is stated with Lean's actual `starRingEnd` expression
so it matches the elaborated complex likelihood exactly. -/
lemma complexGaussianShiftExponent_pair (a : ℝ) (h : ℂ) (x y : ℝ) :
    2 * a * h.re * x - a * h.re ^ 2 + (2 * a * h.im * y - a * h.im ^ 2) =
      2 * a * ((starRingEnd ℂ) h * ({ re := x, im := y } : ℂ)).re -
        a * ‖h‖ ^ 2 := by
  have hcross :
      ((starRingEnd ℂ) h * ({ re := x, im := y } : ℂ)).re =
        h.re * x + h.im * y := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have hnorm : ‖h‖ ^ 2 = h.re ^ 2 + h.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hcross, hnorm]
  ring

end NlsGge.Measure
