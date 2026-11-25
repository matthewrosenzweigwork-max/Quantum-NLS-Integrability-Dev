import QuantumNLS.LOCAL009R22Derivative
import QuantumNLS.LOCAL009R22Ratio
import QuantumNLS.LOCAL009R22Margin

/-! The printed corrected inverse integrand, with its uniform second-order
bound on any source-separated domain satisfying the original phase margins.
The inverse target-disk condition is proved, not supplied as an assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Complex Set Metric
namespace QuantumNLS.LOCAL009R22Integrand
open QuantumNLS.Ext025A7 QuantumNLS.LOCAL009R22Transfer
  QuantumNLS.LOCAL009R22Cauchy QuantumNLS.LOCAL009R22Inverse
  QuantumNLS.LOCAL009R22Derivative QuantumNLS.LOCAL009R22Ratio
  QuantumNLS.LOCAL009R22Margin QuantumNLS.TransferProductCorrection

def correctedIntegrand (κ L M d ε : ℝ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  inverseTransfer κ L (2*M/d) ε q z + (κ^2 * ε / 2 : ℝ) *
    ratio κ L z (inverseTransfer κ L (2*M/d) ε q z) *
      deriv (inverseTransfer κ L (2*M/d) ε q) z

def integrandConstant (κ M d r : ℝ) : ℝ :=
  inverseRemainderConstant κ M d (2*M/d) + κ^2/2 *
    (ratioBound κ (2*M/d) * (displacementConstant κ M d / r) +
      ratioLipschitz κ (2*M/d) * displacementConstant κ M d * (M/d^2))

theorem corrected_integrand_bound
    {κ L M d ε r : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (hM : 0 < M) (hd : 0 < d)
    (hsmall : κ * M / d ≤ 1 / 10000) (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    {N : ℕ} (hN : 0 < N) (hε : 0 ≤ ε) (hεM : ε ≤ M)
    (hbudget : ε * N ≤ M) (q : Fin N → ℝ)
    (hsep : ∀ z ∈ U, ∀ j, d ≤ ‖z - (q j : ℂ)‖)
    {z : ℂ} (hr : 0 < r) (hball : closedBall z r ⊆ U) :
    ‖correctedIntegrand κ L M d ε q z - sourceG ε q z‖ ≤
      integrandConstant κ M d r * ε^2 := by
  let R := 2*M/d
  let T := inverseTransfer κ L R ε q
  let G := sourceG ε q z
  let P := deriv (sourceG ε q) z
  let D := displacementConstant κ M d
  have hR : 0 < R := by dsimp [R]; positivity
  have hradius : κ * R ≤ 1/1000 := by
    calc
      κ * R = 2 * (κ * M / d) := by dsimp [R]; ring
      _ ≤ 1/1000 := by linarith
  have hs : κ * M / d ≤ 1/10 := by linarith
  have hz : z ∈ U := hball (mem_closedBall_self hr.le)
  have hG : ∀ w ∈ U, ‖sourceG ε q w‖ ≤ R := by
    intro w hw
    have hb := norm_sourceG_le hε hd hbudget q (hsep w hw)
    calc
      ‖sourceG ε q w‖ ≤ M/d := hb
      _ ≤ 2 * (M/d) := by linarith [div_pos hM hd]
      _ = R := by dsimp [R]; ring
  have hy : ∀ w ∈ U, ‖transferS (κ*ε) L q w - spectralMap κ L w 0‖ <
      3/4 * ‖spectralLinear κ L w‖ * R := by
    intro w hw
    exact transfer_target_margin hκ hM hd hsmall hN hε hεM hbudget q
      (hsep w hw) (hexp w hw) (hgap w hw)
  have hlin := inverse_transfer_linear hκ hM hd hs hR hradius hU hexp hgap
    hN hε hεM hbudget q hz (hsep z hz) (hG z hz) (hy z hz)
  change ‖T z - G‖ ≤ D * ε at hlin
  have hderiv := inverseTransfer_deriv_sub_bound hκ hM hd hs hR hradius hU hexp hgap
    hN hε hεM hbudget q hsep hG hy hr hball
  change ‖deriv T z - P‖ ≤ (D/r) * ε at hderiv
  have hsecond := inverse_transfer_second_order hκ hM hd hs hR hradius hU hexp hgap
    hN hε hεM hbudget q hz (hsep z hz) (hG z hz) (hy z hz)
  change ‖T z - G + (κ^2 * ε / 2 : ℝ) * ratio κ L z G * P‖ ≤
    inverseRemainderConstant κ M d R * ε^2 at hsecond
  have hTmem : T z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall
    (local009_application κ L hκ hR hradius hU hexp hgap hz (hy z hz)).1
  have hGmem : G ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.mpr (hG z hz)
  have hQ := ratio_norm_le hκ hradius (hexp z hz) (hgap z hz) hTmem
  have hQdiff := ratio_sub_bound hκ hradius (hexp z hz) (hgap z hz) hTmem hGmem
  have hP : ‖P‖ ≤ M/d^2 := norm_deriv_sourceG_le hε hd hbudget q (hsep z hz)
  have hD : 0 ≤ D := by dsimp [D, displacementConstant, transferConstant]; positivity
  have hQ0 : 0 ≤ ratioBound κ R := by unfold ratioBound; positivity
  have hQ1 : 0 ≤ ratioLipschitz κ R := by unfold ratioLipschitz; positivity
  have hdiff : ‖ratio κ L z (T z) * (deriv T z - P) +
      (ratio κ L z (T z) - ratio κ L z G) * P‖ ≤
      (ratioBound κ R * (D/r) + ratioLipschitz κ R * D * (M/d^2)) * ε := by
    calc
      _ ≤ ‖ratio κ L z (T z)‖ * ‖deriv T z - P‖ +
          ‖ratio κ L z (T z) - ratio κ L z G‖ * ‖P‖ := by
        simpa only [norm_mul] using norm_add_le
          (ratio κ L z (T z) * (deriv T z - P))
          ((ratio κ L z (T z) - ratio κ L z G) * P)
      _ ≤ ratioBound κ R * ((D/r) * ε) +
          (ratioLipschitz κ R * (D * ε)) * (M/d^2) := by
        gcongr
        exact hQdiff.trans (mul_le_mul_of_nonneg_left hlin hQ1)
      _ = _ := by ring
  have hα : 0 ≤ κ^2 * ε / 2 := by positivity
  have heq : correctedIntegrand κ L M d ε q z - G =
      (T z - G + (κ^2 * ε / 2 : ℝ) * ratio κ L z G * P) +
      (κ^2 * ε / 2 : ℝ) * (ratio κ L z (T z) * (deriv T z - P) +
        (ratio κ L z (T z) - ratio κ L z G) * P) := by
    change T z + (κ^2 * ε / 2 : ℝ) * ratio κ L z (T z) * deriv T z - G = _
    ring
  rw [heq]
  calc
    _ ≤ ‖T z - G + (κ^2 * ε / 2 : ℝ) * ratio κ L z G * P‖ +
        ‖(κ^2 * ε / 2 : ℝ) * (ratio κ L z (T z) * (deriv T z - P) +
          (ratio κ L z (T z) - ratio κ L z G) * P)‖ := norm_add_le _ _
    _ ≤ inverseRemainderConstant κ M d R * ε^2 + (κ^2 * ε / 2) *
        ((ratioBound κ R * (D/r) + ratioLipschitz κ R * D * (M/d^2)) * ε) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα]
      exact add_le_add hsecond (mul_le_mul_of_nonneg_left hdiff hα)
    _ = _ := by unfold integrandConstant; dsimp [R, D]; ring

end QuantumNLS.LOCAL009R22Integrand
#print axioms QuantumNLS.LOCAL009R22Integrand.corrected_integrand_bound
