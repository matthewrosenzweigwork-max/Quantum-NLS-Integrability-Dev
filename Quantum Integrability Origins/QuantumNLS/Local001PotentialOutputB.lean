import QuantumNLS.Local001PotentialMemLpB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral

noncomputable def potentialResolventOutput {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 ≤ κ) (hL : 0 < L) (n : ℤ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) (f : VectorInterval L) : VectorInterval L :=
  (potentialResolvent_memLp κ hκ hL n hr hsmall hz u f).toLp
    (potentialResolventFn κ u
      (LocalSpectral.resolvent L κ (fun _ => 0) (LocalSpectral.parity n) z f))

#print axioms potentialResolventOutput

theorem potentialResolventOutput_coe {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 ≤ κ) (hL : 0 < L) (n : ℤ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) (f : VectorInterval L) :
    (potentialResolventOutput κ hκ hL n hr hsmall hz u f : ℝ → E2) =ᵐ[LocalSpectral.μI L]
      potentialResolventFn κ u
        (LocalSpectral.resolvent L κ (fun _ => 0) (LocalSpectral.parity n) z f) :=
  (potentialResolvent_memLp κ hκ hL n hr hsmall hz u f).coeFn_toLp

#print axioms potentialResolventOutput_coe

theorem potentialResolventOutput_ae_bound {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 ≤ κ) (hL : 0 < L) (n : ℤ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) (f : VectorInterval L) :
    ∀ᵐ x ∂(LocalSpectral.μI L),
      ‖potentialResolventOutput κ hκ hL n hr hsmall hz u f x‖ ≤
        (2 * Real.sqrt κ * resolventConstant L r * ‖f‖) * ‖u x‖ := by
  have hcoe := potentialResolventOutput_coe κ hκ hL n hr hsmall hz u f
  have hsup := sourceResolvent_ae_sup_bound hL κ n hr hsmall hz f
  filter_upwards [hcoe, hsup] with x hx hu
  rw [hx]
  change ‖potentialPt κ (u x) (LocalSpectral.resolvent L κ
    (fun _ => 0) (LocalSpectral.parity n) z f x)‖ ≤ _
  rw [potentialPt_norm hκ]
  calc
    2 * Real.sqrt κ * ‖u x‖ * ‖LocalSpectral.resolvent L κ
        (fun _ => 0) (LocalSpectral.parity n) z f x‖ ≤
        (2 * Real.sqrt κ * ‖u x‖) * (resolventConstant L r * ‖f‖) := by
          exact mul_le_mul_of_nonneg_left hu (by positivity)
    _ = (2 * Real.sqrt κ * resolventConstant L r * ‖f‖) * ‖u x‖ := by ring


#print axioms potentialResolventOutput_ae_bound


end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
