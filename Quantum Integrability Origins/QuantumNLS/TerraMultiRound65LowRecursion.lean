import QuantumNLS.TerraMultiRound64REG004

/-! Initial steps of the printed signed Riccati recursion. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open QuantumNLS.ClassicalCharges QuantumNLS.TerraMultiRound41Coefficients
namespace QuantumNLS.TerraMultiRound65LowRecursion

theorem aseq_two {L : ℝ} (κ : ℝ) {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    aseq κ f 2 = fun x => -deriv f x := by
  have h := aseq_succ κ hf 0
  simpa [aseq_one] using h

theorem aseq_three {L : ℝ} (κ : ℝ) {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    aseq κ f 3 = fun x => deriv (deriv f) x - (κ : ℂ) * conj (f x) * (f x)^2 := by
  have h := aseq_succ κ hf 1
  rw [aseq_two κ hf] at h
  funext x
  have hp := congrFun h x
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.reduceAdd, Nat.reduceSub,
    aseq_one] at hp
  rw [hp]
  change -deriv (-(deriv f)) x - _ = _
  rw [deriv.neg]
  ring

#print axioms aseq_two
#print axioms aseq_three
end QuantumNLS.TerraMultiRound65LowRecursion
