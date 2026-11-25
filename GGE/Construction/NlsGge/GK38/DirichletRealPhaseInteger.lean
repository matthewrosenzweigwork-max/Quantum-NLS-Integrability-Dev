import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Scalar clockwise half-turn index, independent of Dirichlet/periodic root proofs. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_clockwise_phase_integer38 (θ : ℝ)
    (h : (Complex.exp (-Complex.I * (θ : ℂ))).im = 0) :
    ∃ n : ℤ, θ = (n : ℝ) * Real.pi := by
  have hs : Real.sin θ = 0 := by
    simpa [Complex.exp_im, Complex.mul_re, Complex.mul_im] using h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
  exact ⟨n, hn.symm⟩


end
end NlsGge.GK38
