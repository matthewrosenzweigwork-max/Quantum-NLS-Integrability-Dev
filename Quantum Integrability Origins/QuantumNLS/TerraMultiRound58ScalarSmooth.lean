import QuantumNLS.TerraMultiRound43REG005
import QuantumNLS.TerraMultiRound45ScalarBound

/-! Scalar consequences of a smooth Riccati approximation. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate MeasureTheory Finset
namespace QuantumNLS.TerraMultiRound58ScalarSmooth
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiExpansions
open QuantumNLS.ClassicalCharges QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound41Coefficients
open QuantumNLS.TerraMultiRound45ScalarBound

/-- The scalar error is controlled by the norm error of the Sobolev approximation. -/
theorem scalar_approximation_bound (L : ℝ) (hL : 0 < L) {a : ℝ}
    (ha : 1 / 2 < a) (u r p : Ell2) :
    ‖scalar L a u r - scalar L a u p‖ ≤
      (L * physK L a ^ 2 * ‖u‖) * ‖r - p‖ := by
  rw [← scalar_sub L hL ha]
  calc
    _ ≤ L * ((physK L a * ‖u‖) * (physK L a * ‖r - p‖)) :=
      scalar_norm_le L hL ha u (r - p)
    _ = _ := by ring

/-- Pairing a pointwise smooth recursive approximant yields its coefficient polynomial. -/
theorem scalar_recursive_approximant (L a κ : ℝ) (u p : Ell2)
    (f : ℝ → ℂ) (hf : SmoothPeriodic L f) (hrep : physRep L a u = f)
    (M : ℕ) (Y : ℝ)
    (hp : ∀ t : ℝ, physRep L a p t =
      ∑ n ∈ Finset.Icc 1 M, aseq κ f n t * ((Y : ℂ)⁻¹) ^ n) :
    scalar L a u p = ∑ n ∈ Finset.Icc 1 M,
      coefficient L κ f n * ((Y : ℂ)⁻¹) ^ n := by
  unfold scalar coefficient
  simp_rw [hrep, hp, Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    simp_rw [show ∀ t : ℝ, conj (f t) * (aseq κ f n t * ((Y : ℂ)⁻¹) ^ n) =
      (conj (f t) * aseq κ f n t) * ((Y : ℂ)⁻¹) ^ n by intro t; ring]
    exact intervalIntegral.integral_mul_const _ _
  · intro n hn
    apply Continuous.intervalIntegrable
    apply (Complex.continuous_conj.comp hf.1.continuous).mul
    apply Continuous.mul
    · exact (continuous_const.mul (vseq_regular κ hf n).1.continuous)
    · exact continuous_const

#print axioms scalar_approximation_bound
#print axioms scalar_recursive_approximant
end QuantumNLS.TerraMultiRound58ScalarSmooth
