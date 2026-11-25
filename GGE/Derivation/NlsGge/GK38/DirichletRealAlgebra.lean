import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Typed scalar adapters for actual Dirichlet real-slice assembly. -/
set_option autoImplicit false
namespace NlsGge.GK38

/-- Conjugate matrix entries give the real Dirichlet scalar. -/
theorem dirichlet_scalar_im_zero38 (a b c d : ℂ)
    (ha : a.re = d.re) (hb : b.re = c.re) :
    ((c + d - a - b) / (2 * Complex.I)).im = 0 := by
  simp [Complex.div_im, Complex.normSq, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.add_re]
  linarith

/-- Real part of the actual squared identity with all codomains fixed. -/
theorem dirichlet_scalar_square38 (D : ℂ) (δ : ℝ) (hi : D.im = 0)
    (h : D ^ 2 - 4 = (δ : ℂ) ^ 2) : D.re ^ 2 - 4 = δ ^ 2 := by
  have hD : D = (D.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hi
  rw [hD] at h
  exact_mod_cast h

end NlsGge.GK38
