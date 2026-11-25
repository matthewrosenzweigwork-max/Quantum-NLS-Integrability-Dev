import QuantumNLS.TerraMultiRound51TaylorIntegral

/-! The zero-degree integrated coefficient is the unshifted correlation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound51TaylorLeading
open QuantumNLS.TerraMultiRound48Leading QuantumNLS.TerraMultiRound51TaylorCoeff
open QuantumNLS.TerraMultiRound51TaylorIntegral

theorem pathCoeff_zero {n q : ℕ} (C : (Fin q → ℝ) → ℂ)
    (paths : Fin q → Finset (Fin n)) (t : Fin n → ℝ) :
    pathCoeff C paths 0 t = C 0 := by
  simp [pathCoeff, iteratedFDeriv_zero_apply]

theorem integratedCoeff_zero {n q : ℕ} (C : (Fin q → ℝ) → ℂ)
    (paths : Fin q → Finset (Fin n)) : integratedCoeff C paths 0 = C 0 := by
  unfold integratedCoeff
  simp_rw [pathCoeff_zero, integral_mul_const]
  rw [integral_complex_ofReal, orthant_exp_integral]
  simp

#print axioms pathCoeff_zero
#print axioms integratedCoeff_zero
end QuantumNLS.TerraMultiRound51TaylorLeading
