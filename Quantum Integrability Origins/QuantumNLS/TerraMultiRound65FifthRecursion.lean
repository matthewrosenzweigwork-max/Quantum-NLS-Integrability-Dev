import QuantumNLS.TerraMultiRound65FourthRecursion

/-! The fifth signed Riccati coefficient appearing in REG-008. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open QuantumNLS.ClassicalCharges QuantumNLS.TerraMultiRound41Coefficients
open QuantumNLS.TerraMultiRound65LowRecursion QuantumNLS.TerraMultiRound65FourthRecursion
namespace QuantumNLS.TerraMultiRound65FifthRecursion

theorem aseq_five {L : ℝ} (κ : ℝ) {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    aseq κ f 5 = fun x => deriv (deriv (deriv (deriv f))) x -
      (κ : ℂ) * conj (deriv (deriv f) x) * (f x)^2 -
      6 * (κ : ℂ) * conj (deriv f x) * f x * deriv f x -
      5 * (κ : ℂ) * conj (f x) * (deriv f x)^2 -
      6 * (κ : ℂ) * conj (f x) * f x * deriv (deriv f) x +
      2 * (κ : ℂ)^2 * (conj (f x))^2 * (f x)^3 := by
  have hs1 := (contDiff_infty_iff_deriv.mp hf.smooth).2
  have hs2 := (contDiff_infty_iff_deriv.mp hs1).2
  have hs3 := (contDiff_infty_iff_deriv.mp hs2).2
  have h0 := (contDiff_infty_iff_deriv.mp hf.smooth).1
  have h1 := (contDiff_infty_iff_deriv.mp hs1).1
  have h2 := (contDiff_infty_iff_deriv.mp hs2).1
  have h3 := (contDiff_infty_iff_deriv.mp hs3).1
  have hrec := aseq_succ κ hf 3
  rw [aseq_four κ hf] at hrec
  funext x
  have hf0 := (h0 x).hasDerivAt
  have hf1 := (h1 x).hasDerivAt
  have hf2 := (h2 x).hasDerivAt
  have hf3 := (h3 x).hasDerivAt
  have hp1 := ((hasDerivAt_const x (κ : ℂ)).mul hf1.star).mul (hf0.pow 2)
  have hp2 := ((((hasDerivAt_const x (4 * (κ : ℂ))).mul hf0.star).mul hf0).mul hf1)
  have ht := hf3.neg.add hp1 |>.add hp2
  have ht' : HasDerivAt (fun y => -deriv (deriv (deriv f)) y +
      (κ : ℂ) * conj (deriv f y) * f y^2 +
      4 * (κ : ℂ) * conj (f y) * f y * deriv f y) _ x := ht
  have hh := congrFun hrec x
  simp only [show Finset.Icc 1 3 = {1,2,3} by decide] at hh
  simp [Finset.sum_insert, aseq_one, aseq_two κ hf, aseq_three κ hf] at hh
  rw [hh, ht'.deriv]
  simp only [Pi.mul_apply, Pi.pow_apply, RCLike.star_def]
  ring

#print axioms aseq_five
end QuantumNLS.TerraMultiRound65FifthRecursion
