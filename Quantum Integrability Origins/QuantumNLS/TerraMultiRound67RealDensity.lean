import QuantumNLS.TerraMultiRound66SmoothCorrection

/-! Relating the embedded density derivative in the smooth calculation to the
    printed square of the real density derivative. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open QuantumNLS.TerraMultiRound65DensityDerivative
namespace QuantumNLS.TerraMultiRound67RealDensity

theorem density_embedded_deriv {f : ℝ → ℂ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    deriv (fun y => ((‖f y‖^2 : ℝ) : ℂ)) x =
      ((deriv (fun y => ‖f y‖^2) x : ℝ) : ℂ) := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (density_hasDerivAt hf.hasDerivAt)
  have hr : HasDerivAt (fun y => ‖f y‖^2)
      (Complex.reCLM (conj (deriv f x) * f x + conj (f x) * deriv f x)) x := by
    change HasDerivAt (fun y => Complex.re (((‖f y‖^2 : ℝ) : ℂ)))
      (Complex.reCLM (conj (deriv f x) * f x + conj (f x) * deriv f x)) x at h
    simp only [Complex.ofReal_re] at h
    exact h
  exact (hr.ofReal_comp.deriv).trans (congrArg Complex.ofReal hr.deriv.symm)

theorem density_embedded_deriv_sq {f : ℝ → ℂ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    (deriv (fun y => ((‖f y‖^2 : ℝ) : ℂ)) x)^2 =
      ((‖deriv (fun y => ‖f y‖^2) x‖^2 : ℝ) : ℂ) := by
  rw [density_embedded_deriv hf, ← Complex.ofReal_pow]
  simp only [Real.norm_eq_abs, sq_abs]

#print axioms density_embedded_deriv
#print axioms density_embedded_deriv_sq
end QuantumNLS.TerraMultiRound67RealDensity
