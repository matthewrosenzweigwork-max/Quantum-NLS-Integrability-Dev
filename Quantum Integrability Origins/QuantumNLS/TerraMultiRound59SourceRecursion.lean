import QuantumNLS.TerraMultiRound59FreeRecursion
import QuantumNLS.TerraMultiRound59MinimalPolynomial
import QuantumNLS.TerraMultiRound58AbsoluteParity

/-! The minimal polynomial agrees with the source's smooth recursion formula. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ComplexConjugate
namespace QuantumNLS.TerraMultiRound59SourceRecursion
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.ClassicalCharges QuantumNLS.TerraMultiRound41Coefficients
open QuantumNLS.TerraMultiRound58Compare QuantumNLS.TerraMultiRound58SmoothParity
open QuantumNLS.TerraMultiRound58AbsoluteParity QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.TerraMultiRound59FreeRecursion QuantumNLS.TerraMultiRound59MinimalPolynomial

theorem recursiveDifference_source (L κ : ℝ) {f : ℝ → ℂ} (hf : SmoothPeriodic L f) (j : ℕ) :
    recursiveDifference L κ f (2 * j + 1) =
      ∫ x in (0 : ℝ)..L, conj (f x) * (aseq κ f (2 * j + 1) x - iteratedDeriv (2 * j) f x) := by
  have h1 : IntervalIntegrable (fun x => conj (f x) * aseq κ f (2 * j + 1) x) volume 0 L := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_conj.comp hf.smooth.continuous).mul
      (continuous_const.mul (vseq_regular κ hf (2 * j + 1)).1.continuous)
  have h2 : IntervalIntegrable (fun x => conj (f x) * iteratedDeriv (2 * j) f x) volume 0 L := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_conj.comp hf.smooth.continuous).mul
      (hf.smooth.continuous_iteratedDeriv (2 * j) (by change (((2 * j : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
  simp only [recursiveDifference, show 2 * j + 1 ≠ 0 by omega, if_false, coefficient,
    free_aseq_odd hf]
  rw [← intervalIntegral.integral_sub h1 h2]
  apply intervalIntegral.integral_congr
  intro x hx
  ring

theorem R_source_smooth (L : ℝ) [Fact (0 < L)] (j : ℕ) (hj : 2 ≤ j)
    (κ : ℝ) (hκ : 0 < κ) (x : Ell2) (f : ℝ → ℂ)
    (hrep : physRep L (j - 1 : ℕ) x = f) (hf : SmoothPeriodic L f) :
    ((R (L := L) j hj κ x : ℝ) : ℂ) = ((-1 : ℂ) ^ j) *
      ∫ y in (0 : ℝ)..L, conj (f y) * (aseq κ f (2 * j + 1) y - iteratedDeriv (2 * j) f y) := by
  have hr := R_smooth_recursion (L := L) j hj κ x f hrep hf
  have hc := tree_coefficient_smooth L j hj κ x f hrep hf (2 * j + 1) le_rfl
  have hp := (smooth_tree_coefficient_parity L j hj κ hκ x f hrep hf).2 j le_rfl
  rw [hc] at hp
  have hs : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
  have hre : R (L := L) j hj κ x = (-1 : ℝ) ^ j * (recursiveDifference L κ f (2 * j + 1)).re := by
    rw [hr, ← mul_assoc, hs, one_mul]
  rw [← recursiveDifference_source L κ hf j]
  rw [show (-1 : ℂ) ^ j = (((-1 : ℝ) ^ j : ℝ) : ℂ) by push_cast; rfl]
  apply Complex.ext
  · simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact hre
  · simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, hp, mul_zero, zero_mul, add_zero]

#print axioms recursiveDifference_source
#print axioms R_source_smooth
end QuantumNLS.TerraMultiRound59SourceRecursion
