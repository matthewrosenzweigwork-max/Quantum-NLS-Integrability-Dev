import QuantumNLS.LOCAL009R22Inverse
import Mathlib.Analysis.Complex.Liouville

/-! Cauchy's estimate for the entire z-dependence of g_z(s_ε(z)).
In particular this is not a derivative with g_z held fixed. -/
set_option autoImplicit false
noncomputable section
open Complex Set Metric
namespace QuantumNLS.LOCAL009R22Derivative
open QuantumNLS.Ext025A7 QuantumNLS.LOCAL009R22Transfer
  QuantumNLS.LOCAL009R22Cauchy QuantumNLS.LOCAL009R22Inverse
  QuantumNLS.TransferProductCorrection

theorem transfer_analyticAt (c L : ℝ) {N : ℕ} (q : Fin N → ℝ)
    {z : ℂ} (hsep : ∀ j, z ≠ (q j : ℂ)) :
    AnalyticAt ℂ (transferS c L q) z := by
  have ha : ∀ j, AnalyticAt ℂ (fun w : ℂ => I * c / (w - (q j : ℂ))) z := by
    intro j
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (hsep j))
  have hp : AnalyticAt ℂ (fun w : ℂ => ∏ j, (1 + I * c / (w - (q j : ℂ)))) z := Finset.univ.analyticAt_fun_prod
    (fun j _ => analyticAt_const.add (ha j))
  have hm : AnalyticAt ℂ (fun w : ℂ => ∏ j, (1 - I * c / (w - (q j : ℂ)))) z := Finset.univ.analyticAt_fun_prod
    (fun j _ => analyticAt_const.sub (ha j))
  have he : AnalyticAt ℂ (fun w : ℂ => Complex.exp (I * w * L)) z := by
    fun_prop
  exact hp.add (he.mul hm)

def inverseTransfer (κ L R ε : ℝ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  spectralInverse κ L R z (transferS (κ * ε) L q z)

theorem inverseTransfer_analyticAt {κ L R ε : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (hR : 0 < R) (hradius : κ * R ≤ 1 / 1000)
    (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    {N : ℕ} (q : Fin N → ℝ) {z : ℂ} (hz : z ∈ U)
    (hsep : ∀ j, z ≠ (q j : ℂ))
    (htarget : ‖transferS (κ * ε) L q z - spectralMap κ L z 0‖ <
      3 / 4 * ‖spectralLinear κ L z‖ * R) :
    AnalyticAt ℂ (inverseTransfer κ L R ε q) z := by
  have h := (local009_application κ L hκ hR hradius hU hexp hgap hz htarget).2.2.2.1
  exact h.comp (f := fun w : ℂ => (w, transferS (κ * ε) L q w))
    (analyticAt_id.prod (transfer_analyticAt (κ * ε) L q hsep))

/-- Uniform first-order displacement on a neighborhood gives the printed
first-order bound for the derivative on the contour. All pointwise inverse
displacement bounds used here are proved by `inverse_transfer_linear`. -/
theorem inverseTransfer_deriv_sub_bound
    {κ L M d ε R r : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (hM : 0 < M) (hd : 0 < d)
    (hsmall : κ * M / d ≤ 1 / 10)
    (hR : 0 < R) (hradius : κ * R ≤ 1 / 1000) (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    {N : ℕ} (hN : 0 < N) (hε : 0 ≤ ε) (hεM : ε ≤ M)
    (hbudget : ε * N ≤ M) (q : Fin N → ℝ)
    (hsep : ∀ z ∈ U, ∀ j, d ≤ ‖z - (q j : ℂ)‖)
    (hG : ∀ z ∈ U, ‖sourceG ε q z‖ ≤ R)
    (htarget : ∀ z ∈ U,
      ‖transferS (κ * ε) L q z - spectralMap κ L z 0‖ <
        3 / 4 * ‖spectralLinear κ L z‖ * R)
    {z : ℂ} (hr : 0 < r) (hball : closedBall z r ⊆ U) :
    ‖deriv (inverseTransfer κ L R ε q) z - deriv (sourceG ε q) z‖ ≤
      (displacementConstant κ M d / r) * ε := by
  have hn : ∀ w ∈ U, ∀ j, w ≠ (q j : ℂ) := by
    intro w hw j he
    have := hsep w hw j
    rw [he, sub_self, norm_zero] at this
    linarith
  have hT : ∀ w ∈ U, DifferentiableAt ℂ (inverseTransfer κ L R ε q) w :=
    fun w hw => (inverseTransfer_analyticAt hκ hR hradius hU hexp hgap q hw
      (hn w hw) (htarget w hw)).differentiableAt
  have hGd : ∀ w ∈ U, DifferentiableAt ℂ (sourceG ε q) w :=
    fun w hw => (hasDerivAt_sourceG ε q (hn w hw)).differentiableAt
  have hdiff : DifferentiableOn ℂ
      (fun w => inverseTransfer κ L R ε q w - sourceG ε q w) U :=
    fun w hw => ((hT w hw).sub (hGd w hw)).differentiableWithinAt
  have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (hdiff.diffContOnCl_ball hball) (fun w hw =>
      inverse_transfer_linear hκ hM hd hsmall hR hradius hU hexp hgap
        hN hε hεM hbudget q (hball (sphere_subset_closedBall hw))
        (hsep w (hball (sphere_subset_closedBall hw)))
        (hG w (hball (sphere_subset_closedBall hw)))
        (htarget w (hball (sphere_subset_closedBall hw))))
  have hz := hball (mem_closedBall_self hr.le)
  rw [deriv_fun_sub (hT z hz) (hGd z hz)] at hbound
  convert hbound using 1
  ring

end QuantumNLS.LOCAL009R22Derivative
#print axioms QuantumNLS.LOCAL009R22Derivative.transfer_analyticAt
#print axioms QuantumNLS.LOCAL009R22Derivative.inverseTransfer_analyticAt
#print axioms QuantumNLS.LOCAL009R22Derivative.inverseTransfer_deriv_sub_bound
