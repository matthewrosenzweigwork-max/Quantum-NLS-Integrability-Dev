import QuantumNLS.TerraMultiRound65LowRecursion
import Mathlib.Analysis.Calculus.Deriv.Star

/-! The fourth coefficient in the printed Riccati recursion. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open QuantumNLS.ClassicalCharges QuantumNLS.TerraMultiRound41Coefficients
open QuantumNLS.TerraMultiRound65LowRecursion
namespace QuantumNLS.TerraMultiRound65FourthRecursion

theorem aseq_four {L : ℝ} (κ : ℝ) {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    aseq κ f 4 = fun x => -deriv (deriv (deriv f)) x +
      (κ : ℂ) * conj (deriv f x) * (f x)^2 +
      4 * (κ : ℂ) * conj (f x) * f x * deriv f x := by
  have hd := (contDiff_infty_iff_deriv.mp hf.smooth).1
  have hdd := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf.smooth).2).1
  have hddd := (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf.smooth).2).2).1
  have hrec := aseq_succ κ hf 2
  rw [aseq_three κ hf] at hrec
  funext x
  have hv := hd x
  have hv2 := hddd x
  have hprod : HasDerivAt (fun y => (κ : ℂ) * conj (f y) * f y^2)
      ((κ : ℂ) * conj (deriv f x) * f x^2 +
        (κ : ℂ) * conj (f x) * (2 * f x * deriv f x)) x := by
    convert ((hasDerivAt_const x (κ : ℂ)).mul hv.hasDerivAt.star).mul (hv.hasDerivAt.pow 2) using 1
    · funext y; rfl
    · simp
  have hmain := hv2.hasDerivAt.sub hprod
  have hp := congrFun hrec x
  simp only [show Finset.Icc 1 2 = {1,2} by decide] at hp
  simp [Finset.sum_insert, aseq_one, aseq_two κ hf] at hp
  have hmain' : HasDerivAt (fun y => deriv (deriv f) y - (κ : ℂ) * conj (f y) * f y^2)
      (deriv (deriv (deriv f)) x - ((κ : ℂ) * conj (deriv f x) * f x^2 +
        (κ : ℂ) * conj (f x) * (2 * f x * deriv f x))) x := hmain
  rw [hp, hmain'.deriv]
  ring

#print axioms aseq_four
end QuantumNLS.TerraMultiRound65FourthRecursion
