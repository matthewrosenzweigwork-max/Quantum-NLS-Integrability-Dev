import QuantumNLS.TerraMultiRound45Iterates
import QuantumNLS.TerraMultiRound40ScalarParity
import QuantumNLS.RiccatiClassical
import QuantumNLS.RiccatiJBound

/-! The all-order Picard error controls the physical scalar integral.
This is a supporting bound, not the REG-007 scalar expansion. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate MeasureTheory
namespace QuantumNLS.TerraMultiRound45ScalarBound
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiExpansions
open QuantumNLS.RiccatiClassical QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound45Iterates

/-- The scalar pairing is bounded on the Fourier Sobolev space. -/
theorem scalar_norm_le (L : ℝ) (hL : 0 < L) {a : ℝ} (ha : 1 / 2 < a)
    (u v : Ell2) : ‖scalar L a u v‖ ≤ L * ((physK L a * ‖u‖) * (physK L a * ‖v‖)) := by
  have hpk : 0 ≤ physK L a := physK_nonneg (by linarith)
  exact QuantumNLS.RiccatiJBound.norm_J_le hL.le (mul_nonneg hpk (norm_nonneg _))
    (fun t _ => physRep_norm_le hL ha u t)
    (fun t _ => physRep_norm_le hL ha v t)

/-- The integral of a difference is the difference of scalar pairings. -/
theorem scalar_sub (L : ℝ) (hL : 0 < L) {a : ℝ} (ha : 1 / 2 < a)
    (u v w : Ell2) : scalar L a u (v - w) = scalar L a u v - scalar L a u w := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hu := physRep_continuous L ha u
  have hv := physRep_continuous L ha v
  have hw := physRep_continuous L ha w
  unfold scalar
  simp only [physRep_sub_apply hL ha, mul_sub]
  simpa only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply] using
    (intervalIntegral.integral_sub
      (((Complex.continuous_conj.comp hu).mul hv).intervalIntegrable (0 : ℝ) L)
      (((Complex.continuous_conj.comp hu).mul hw).intervalIntegrable (0 : ℝ) L))

/-- The scalar difference after n iterates has a cubic error times the
n-th power of the quadratic contraction rate. -/
theorem scalar_iterate_error (L : ℝ) (hL : 0 < L) {a Y : ℝ} (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2)
    (hsmall : 16 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 ≤ |Y| ^ 2)
    (hr : physicalT hL ha hY κ u r = r)
    (hn : ‖r‖ ≤ 2 * ‖u‖ / |Y|) (n : ℕ) :
    ‖scalar L a u r - scalar L a u (iterate hL ha hY κ u n)‖ ≤
      (L * physK L a ^ 2 * ‖u‖) *
      ((8 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 / |Y| ^ 2) ^ n *
      ((4 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 3) * |Y|⁻¹ ^ 3)) := by
  rw [← scalar_sub L hL ha]
  have hb := scalar_norm_le L hL ha u (r - iterate hL ha hY κ u n)
  have he := iterate_error hL ha hY κ u r hsmall hr hn n
  have hc : 0 ≤ L * physK L a ^ 2 * ‖u‖ := by positivity
  calc
    _ ≤ L * (physK L a * ‖u‖ * (physK L a * ‖r - iterate hL ha hY κ u n‖)) := hb
    _ = (L * physK L a ^ 2 * ‖u‖) * ‖r - iterate hL ha hY κ u n‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he hc

#print axioms scalar_norm_le
#print axioms scalar_sub
#print axioms scalar_iterate_error
end QuantumNLS.TerraMultiRound45ScalarBound
