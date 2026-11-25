import Mathlib

/-! Regularized even-moment kernels for the REG-004 induction. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound60Kernel

/-- The positive kernel used in the printed induction. -/
def kernel (s : ℕ) (Y t : ℝ) : ℝ := Y^2 * t^(2*s) / (Y^2+t^2)

theorem kernel_nonneg (s : ℕ) (Y t : ℝ) : 0 ≤ kernel s Y t := by
  unfold kernel
  exact div_nonneg (mul_nonneg (sq_nonneg Y) ((even_two_mul s).pow_nonneg t))
    (add_nonneg (sq_nonneg Y) (sq_nonneg t))

theorem kernel_succ (s : ℕ) (Y t : ℝ) (hY : 0 < Y) :
    kernel (s+1) Y t = Y^2 * t^(2*s) - Y^2 * kernel s Y t := by
  have hd : Y^2+t^2 ≠ 0 := by positivity
  unfold kernel
  rw [show 2*(s+1) = 2*s+2 by omega, pow_add]
  field_simp
  <;> ring

theorem kernel_le_previous (s : ℕ) (Y t : ℝ) (hY : 0 < Y) :
    kernel (s+1) Y t ≤ Y^2 * t^(2*s) := by
  rw [kernel_succ s Y t hY]
  have h := kernel_nonneg s Y t
  nlinarith [sq_nonneg Y, mul_nonneg (sq_nonneg Y) h]

theorem kernel_mono (s : ℕ) (Y Z t : ℝ) (hY : 0 < Y) (hYZ : Y ≤ Z) :
    kernel s Y t ≤ kernel s Z t := by
  have hZ : 0 < Z := lt_of_lt_of_le hY hYZ
  have hdy : 0 < Y^2+t^2 := by positivity
  have hdz : 0 < Z^2+t^2 := by positivity
  unfold kernel
  apply (div_le_div_iff₀ hdy hdz).2
  have hp : 0 ≤ t^(2*s) := even_two_mul s |>.pow_nonneg t
  have hsq : Y^2 ≤ Z^2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (mul_nonneg hp (sq_nonneg t))]

#print axioms kernel_nonneg
#print axioms kernel_succ
#print axioms kernel_le_previous
#print axioms kernel_mono
end QuantumNLS.TerraMultiRound60Kernel
