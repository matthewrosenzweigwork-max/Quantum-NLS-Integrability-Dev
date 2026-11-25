import QuantumNLS.TerraMultiRound41Coefficients

/-! The zero-coupling recursion is the alternating derivative sequence. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59FreeRecursion
open QuantumNLS.ClassicalCharges QuantumNLS.TerraMultiRound41Coefficients

theorem free_aseq {L : ℝ} {f : ℝ → ℂ} (hf : SmoothPeriodic L f) (n : ℕ) :
    aseq 0 f (n + 1) = fun x => (-1 : ℂ) ^ n * iteratedDeriv n f x := by
  induction n with
  | zero => simp [aseq_one]
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, aseq_succ 0 hf n, ih]
    funext x
    simp only [Complex.ofReal_zero, zero_mul, sub_zero]
    rw [deriv_const_mul_field, iteratedDeriv_succ, pow_succ]
    ring

theorem free_aseq_odd {L : ℝ} {f : ℝ → ℂ} (hf : SmoothPeriodic L f) (j : ℕ) :
    aseq 0 f (2 * j + 1) = iteratedDeriv (2 * j) f := by
  rw [free_aseq hf (2 * j)]
  funext x
  have he : (-1 : ℂ) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
  rw [he, one_mul]

#print axioms free_aseq
#print axioms free_aseq_odd
end QuantumNLS.TerraMultiRound59FreeRecursion
