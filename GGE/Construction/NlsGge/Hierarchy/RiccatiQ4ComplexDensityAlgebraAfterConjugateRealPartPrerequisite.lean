import NlsGge.Hierarchy.RiccatiQ4ComplexScalarNormalizationPrerequisite
import NlsGge.Hierarchy.RiccatiQ4ConjugateRealPartAdditionPrerequisite

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati

open scoped ComplexConjugate

/-- The complex algebra underlying the actual Q₄ density split, with the
second-derivative value kept as an independent coefficient. -/
theorem q4ComplexDensityAlgebraAfterConjugateRealPartPrerequisite (c d e : ℂ) :
    Complex.re
      (e * star e + d ^ 2 * star c ^ 2 + c ^ 2 * star d ^ 2 +
        8 * c * star c * d * star d + 2 * c ^ 3 * star c ^ 3) =
      ‖e‖ ^ 2 +
        (2 * Complex.re ((star c * d) ^ 2) +
          8 * ‖c‖ ^ 2 * ‖d‖ ^ 2 + 2 * ‖c‖ ^ 6) := by
  have hmul (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    have hmul' : z * star z = ((‖z‖ : ℂ) ^ 2) := by
      simpa only [RCLike.star_def] using!
        (RCLike.mul_conj z)
    calc
      z * star z = ((‖z‖ : ℂ) ^ 2) := hmul'
      _ = ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [← Complex.ofReal_pow]
  have hpair :
      Complex.re (d ^ 2 * star c ^ 2) +
        Complex.re (c ^ 2 * star d ^ 2) =
          2 * Complex.re ((star c * d) ^ 2) := by
    have hfirst : d ^ 2 * star c ^ 2 = (star c * d) ^ 2 := by ring
    have hsecond : c ^ 2 * star d ^ 2 = star ((star c * d) ^ 2) := by
      simp only [star_mul, star_pow, star_star]
      ring
    rw [hfirst, hsecond]
    simpa only [Complex.add_re] using
      q4ConjugateRealPartAddition ((star c * d) ^ 2)
  have hcross :
      Complex.re (8 * c * star c * d * star d) =
        8 * ‖c‖ ^ 2 * ‖d‖ ^ 2 := by
    calc
      _ = Complex.re (8 * (c * star c) * (d * star d)) := by
        congr 1 <;> ring
      _ = Complex.re (8 * ((‖c‖ ^ 2 : ℝ) : ℂ) *
            ((‖d‖ ^ 2 : ℝ) : ℂ)) := by rw [hmul c, hmul d]
      _ = 8 * ‖c‖ ^ 2 * ‖d‖ ^ 2 := by
        change Complex.re (((8 : ℝ) : ℂ) *
          ((‖c‖ ^ 2 : ℝ) : ℂ) * ((‖d‖ ^ 2 : ℝ) : ℂ)) = _
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpow : c ^ 3 * star c ^ 3 = (c * star c) ^ 3 := by
    calc
      c ^ 3 * star c ^ 3 = c ^ 3 * star (c ^ 3) := by
        rw [← q4StarPow c 3]
      _ = (c * star c) ^ 3 := by rw [q4StarPow c 3]; ring
  have hsix : Complex.re (2 * c ^ 3 * star c ^ 3) = 2 * ‖c‖ ^ 6 := by
    calc
      _ = Complex.re (2 * (c ^ 3 * star c ^ 3)) := by congr 1 <;> ring
      _ = Complex.re (2 * (c * star c) ^ 3) := by rw [hpow]
      _ = Complex.re (2 * (((‖c‖ ^ 2 : ℝ) : ℂ) ^ 3)) := by
        rw [hmul c]
      _ = 2 * ‖c‖ ^ 6 := by
        change Complex.re (((2 : ℝ) : ℂ) *
          (((‖c‖ ^ 2 : ℝ) : ℂ) ^ 3)) = _
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
        ring
  have hsplit :
      Complex.re
        (e * star e + d ^ 2 * star c ^ 2 + c ^ 2 * star d ^ 2 +
          8 * c * star c * d * star d + 2 * c ^ 3 * star c ^ 3) =
        Complex.re (e * star e) +
          (Complex.re (d ^ 2 * star c ^ 2) +
            Complex.re (c ^ 2 * star d ^ 2)) +
          Complex.re (8 * c * star c * d * star d) +
          Complex.re (2 * c ^ 3 * star c ^ 3) := by
    simp only [Complex.add_re]
    ring
  rw [hsplit, hmul e, hpair, hcross, hsix]
  simp only [Complex.ofReal_re]
  ring

end NlsGge.HierarchyRiccati

end
