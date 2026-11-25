import QuantumNLS.LOCAL009R22Transfer

/-! Source-normalized root Cauchy sum. These bounds use distance to every
root, and therefore apply on a full neighborhood of a separated rectangle.
The constants do not depend on the tuple, its labels, or its length. -/
set_option autoImplicit false
noncomputable section
open Complex Finset Set
namespace QuantumNLS.LOCAL009R22Cauchy
open QuantumNLS.LOCAL009R22Transfer QuantumNLS.TransferProductCorrection

theorem sourceG_eq_sum (ε : ℝ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) :
    sourceG ε q z = (ε : ℂ) * ∑ j, (z - (q j : ℂ))⁻¹ := by
  by_cases hn : N = 0
  · subst hn
    simp [sourceG, cauchyG]
  · have hnc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [sourceG, cauchyG, Complex.ofReal_natCast]
    field_simp

theorem hasDerivAt_sourceG (ε : ℝ) {N : ℕ} (q : Fin N → ℝ) {z : ℂ}
    (hz : ∀ j, z ≠ (q j : ℂ)) :
    HasDerivAt (sourceG ε q)
      (-(ε : ℂ) * ∑ j, ((z - (q j : ℂ)) ^ 2)⁻¹) z := by
  have hd := (hasDerivAt_cauchyG_separated q hz).const_mul
    (ε * (N : ℝ) : ℂ)
  change HasDerivAt (sourceG ε q) _ z at hd
  convert hd using 1
  by_cases hn : N = 0
  · subst hn
    simp
  · have hnc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    push_cast
    field_simp

theorem norm_sourceG_le {ε M d : ℝ} (hε : 0 ≤ ε) (hd : 0 < d)
    {N : ℕ} (hbudget : ε * N ≤ M) (q : Fin N → ℝ) {z : ℂ}
    (hsep : ∀ j, d ≤ ‖z - (q j : ℂ)‖) :
    ‖sourceG ε q z‖ ≤ M / d := by
  rw [sourceG_eq_sum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hε]
  calc
    ε * ‖∑ j, (z - (q j : ℂ))⁻¹‖ ≤ ε * ∑ j, ‖(z - (q j : ℂ))⁻¹‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hε
    _ ≤ ε * ∑ _j : Fin N, d⁻¹ := by
      gcongr with j
      rw [norm_inv]
      exact inv_anti₀ hd (hsep j)
    _ = (ε * N) / d := by simp; ring
    _ ≤ M / d := div_le_div_of_nonneg_right hbudget hd.le

theorem norm_deriv_sourceG_le {ε M d : ℝ} (hε : 0 ≤ ε) (hd : 0 < d)
    {N : ℕ} (hbudget : ε * N ≤ M) (q : Fin N → ℝ) {z : ℂ}
    (hsep : ∀ j, d ≤ ‖z - (q j : ℂ)‖) :
    ‖deriv (sourceG ε q) z‖ ≤ M / d^2 := by
  have hz : ∀ j, z ≠ (q j : ℂ) := by
    intro j he
    have := hsep j
    rw [he, sub_self, norm_zero] at this
    linarith
  rw [(hasDerivAt_sourceG ε q hz).deriv, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
  calc
    ε * ‖∑ j, ((z - (q j : ℂ))^2)⁻¹‖ ≤
        ε * ∑ j, ‖((z - (q j : ℂ))^2)⁻¹‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hε
    _ ≤ ε * ∑ _j : Fin N, (d⁻¹)^2 := by
      gcongr with j
      rw [norm_inv, norm_pow, ← inv_pow]
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hd (hsep j)) 2
    _ = (ε * N) / d^2 := by simp; ring
    _ ≤ M / d^2 := div_le_div_of_nonneg_right hbudget (sq_nonneg d)

end QuantumNLS.LOCAL009R22Cauchy
#print axioms QuantumNLS.LOCAL009R22Cauchy.sourceG_eq_sum
#print axioms QuantumNLS.LOCAL009R22Cauchy.hasDerivAt_sourceG
#print axioms QuantumNLS.LOCAL009R22Cauchy.norm_sourceG_le
#print axioms QuantumNLS.LOCAL009R22Cauchy.norm_deriv_sourceG_le
