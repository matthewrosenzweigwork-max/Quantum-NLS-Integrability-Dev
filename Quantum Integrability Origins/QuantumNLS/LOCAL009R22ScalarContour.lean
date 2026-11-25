import QuantumNLS.LOCAL009R22Integrand
import QuantumNLS.LOCAL009R22Residues

/-! Scalar contour assembly for the printed corrected inverse expression.
The domain hypotheses are elementary phase/separation estimates. The inverse
selection, its target margin, the expansion, and its total z-derivative are
proved upstream, rather than assumed in this theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Complex Set Metric Interval
namespace QuantumNLS.LOCAL009R22ScalarContour
open QuantumNLS.Ext025A7 QuantumNLS.LOCAL009R22Transfer
  QuantumNLS.LOCAL009R22Cauchy QuantumNLS.LOCAL009R22Inverse
  QuantumNLS.LOCAL009R22Derivative QuantumNLS.LOCAL009R22Ratio
  QuantumNLS.LOCAL009R22Margin QuantumNLS.LOCAL009R22Integrand
  QuantumNLS.LOCAL009R22Residues QuantumNLS.TransferProductCorrection
  QuantumNLS.LabelExactPeriod QuantumNLS.PeriodTwoTerm QuantumNLS.PeriodReconstruction

theorem correctedIntegrand_continuousAt
    {κ L M d ε : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (hM : 0 < M) (hd : 0 < d)
    (hsmall : κ * M / d ≤ 1 / 10000) (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    {N : ℕ} (hN : 0 < N) (hε : 0 ≤ ε) (hεM : ε ≤ M)
    (hbudget : ε * N ≤ M) (q : Fin N → ℝ)
    (hsep : ∀ z ∈ U, ∀ j, d ≤ ‖z - (q j : ℂ)‖)
    {z : ℂ} (hz : z ∈ U) :
    ContinuousAt (correctedIntegrand κ L M d ε q) z := by
  let R := 2*M/d
  let T := inverseTransfer κ L R ε q
  have hR : 0 < R := by dsimp [R]; positivity
  have hradius : κ * R ≤ 1/1000 := by
    calc
      κ * R = 2 * (κ * M / d) := by dsimp [R]; ring
      _ ≤ 1/1000 := by linarith
  have hy := transfer_target_margin hκ hM hd hsmall hN hε hεM hbudget q
    (hsep z hz) (hexp z hz) (hgap z hz)
  have hn : ∀ j, z ≠ (q j : ℂ) := by
    intro j he
    have := hsep z hz j
    rw [he, sub_self, norm_zero] at this
    linarith
  have hTa : AnalyticAt ℂ T z := inverseTransfer_analyticAt hκ hR hradius hU
    hexp hgap q hz hn hy
  have hTc : ContinuousAt T z := hTa.continuousAt
  have hTd : ContinuousAt (deriv T) z := hTa.deriv.continuousAt
  have hFc : ContinuousAt (fun w => spectralMap κ L w (T w)) z := by
    unfold spectralMap
    fun_prop
  have hDc : ContinuousAt (fun w => spectralDerivative κ L w (T w)) z := by
    unfold spectralDerivative
    fun_prop
  have hTmem : T z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall
    (local009_application κ L hκ hR hradius hU hexp hgap hz hy).1
  have hDlo := derivative_lower hκ hradius (hexp z hz) (hgap z hz) hTmem
  have hDne : spectralDerivative κ L z (T z) ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  exact hTc.add ((continuousAt_const.mul (hFc.div hDc hDne)).mul hTd)

lemma rectIntegral_sub {F G : ℂ → ℂ} {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h)
    (hF : ∀ z ∈ Gam a b h, ContinuousAt F z)
    (hG : ∀ z ∈ Gam a b h, ContinuousAt G z) :
    rectIntegral (fun z => F z - G z) a b h =
      rectIntegral F a b h - rectIntegral G a b h := by
  have hn : (fun z => F z - G z) = (fun z => F z + (-1 : ℂ) * G z) := by
    funext z
    ring
  rw [hn, rectIntegral_add (f := F) (g := fun z => (-1 : ℂ) * G z)
    hab hh hF (fun z hz => continuousAt_const.mul (hG z hz)),
    rectIntegral_const_mul]
  ring

def scalarApproximation (κ L M d ε a b h : ℝ) {N : ℕ} (q : Fin N → ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * rectIntegral (correctedIntegrand κ L M d ε q) a b h

/-- The scalar GP-17 contour estimate, uniformly in arbitrary root tuples
and rectangle translations, on a domain with the printed phase/separation
margins. In particular the count is a residue count, not a Hamiltonian
Riesz projection. -/
theorem scalar_contour_second_order
    {κ L M d ε r a b h : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (hM : 0 < M) (hd : 0 < d)
    (hsmall : κ * M / d ≤ 1 / 10000) (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    {N : ℕ} (hN : 0 < N) (hε : 0 ≤ ε) (hεM : ε ≤ M)
    (hbudget : ε * N ≤ M) (q : Fin N → ℝ)
    (hsep : ∀ z ∈ U, ∀ j, d ≤ ‖z - (q j : ℂ)‖)
    (hab : a < b) (hh : 0 < h) (hr : 0 < r)
    (hball : ∀ z ∈ Gam a b h, closedBall z r ⊆ U) :
    ‖scalarApproximation κ L M d ε a b h q -
        (ε : ℂ) * ((Finset.univ.filter (fun j => a < q j ∧ q j < b)).card : ℂ)‖ ≤
      (‖(2 * Real.pi * I : ℂ)⁻¹‖ * (2*(b-a)+4*h) *
        integrandConstant κ M d r) * ε^2 := by
  have hcont : Gam a b h ⊆ U := fun z hz => hball z hz (mem_closedBall_self hr.le)
  have hn : ∀ z ∈ U, ∀ j, z ≠ (q j : ℂ) := by
    intro z hz j he
    have := hsep z hz j
    rw [he, sub_self, norm_zero] at this
    linarith
  have hqa : ∀ j, q j ≠ a := by
    intro j he
    have ha : (a : ℂ) + (0 : ℝ) * I ∈ Gam a b h :=
      left_mem hh.le (by rw [uIcc_of_le (by linarith)]; constructor <;> linarith)
    have hn' := hn _ (hcont ha) j
    apply hn'
    simp [he]
  have hqb : ∀ j, q j ≠ b := by
    intro j he
    have hb : (b : ℂ) + (0 : ℝ) * I ∈ Gam a b h :=
      right_mem hh.le (by rw [uIcc_of_le (by linarith)]; constructor <;> linarith)
    have hn' := hn _ (hcont hb) j
    apply hn'
    simp [he]
  have hcount := root_cauchy_contour_count (ε := ε) hab hh q hqa hqb
  have hGeq : (sourceG ε q) = (fun z => (ε : ℂ) * ∑ j, (z - (q j : ℂ))⁻¹) :=
    funext (sourceG_eq_sum ε q)
  rw [← hGeq] at hcount
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hnormalized : (2 * Real.pi * I : ℂ)⁻¹ * rectIntegral (sourceG ε q) a b h =
      (ε : ℂ) * ((Finset.univ.filter (fun j => a < q j ∧ q j < b)).card : ℂ) := by
    rw [hcount]
    field_simp
  have hsub := rectIntegral_sub hab.le hh.le
    (fun z hz => correctedIntegrand_continuousAt hκ hM hd hsmall hU hexp hgap
      hN hε hεM hbudget q hsep (hcont hz))
    (fun z hz => (hasDerivAt_sourceG ε q (hn z (hcont hz))).continuousAt)
  rw [← hnormalized]
  unfold scalarApproximation
  rw [← mul_sub, ← hsub, norm_mul]
  have hb := contour_error_from_uniform_bound hab.le hh.le
    (correctedIntegrand κ L M d ε q) (sourceG ε q)
    (fun z hz => corrected_integrand_bound hκ hM hd hsmall hU hexp hgap
      hN hε hεM hbudget q hsep hr (hball z hz))
  calc
    _ ≤ ‖(2 * Real.pi * I : ℂ)⁻¹‖ *
        ((2*(b-a)+4*h) * (integrandConstant κ M d r * ε^2)) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by ring

end QuantumNLS.LOCAL009R22ScalarContour
#print axioms QuantumNLS.LOCAL009R22ScalarContour.correctedIntegrand_continuousAt
#print axioms QuantumNLS.LOCAL009R22ScalarContour.rectIntegral_sub
#print axioms QuantumNLS.LOCAL009R22ScalarContour.scalar_contour_second_order
