import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! The integrating-factor identity for an actual closed logarithmic ODE.
This allows all integer winding periods; it does not assert period zero.
-/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.Analysis.NonvanishingLoop

def ClosedLogarithmicODETarget : Prop :=
  ∀ (g h : ℝ → ℂ) (T : ℝ), Continuous h →
    (∀ t : ℝ, HasDerivAt g (h t * g t) t) →
    g T = g 0 → g 0 ≠ 0 →
    IntervalIntegrable h volume 0 T ∧
      Complex.exp (∫ t in (0 : ℝ)..T, h t) = 1

theorem exp_integral_eq_one_of_closed_logarithmic_ODE
    (g h : ℝ → ℂ) (T : ℝ) (hh : Continuous h)
    (hg : ∀ t : ℝ, HasDerivAt g (h t * g t) t)
    (hclosed : g T = g 0) (h0 : g 0 ≠ 0) :
    IntervalIntegrable h volume 0 T ∧
      Complex.exp (∫ t in (0 : ℝ)..T, h t) = 1 := by
  have hi : ∀ t : ℝ, IntervalIntegrable h volume 0 t :=
    fun t => hh.intervalIntegrable 0 t
  let P : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, h s
  have hP : ∀ t : ℝ, HasDerivAt P (h t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hi t)
      hh.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt
  let F : ℝ → ℂ := fun t => Complex.exp (-P t) * g t
  have hF : ∀ t : ℝ, HasDerivAt F 0 t := by
    intro t
    have hd := ((hP t).neg.cexp).mul (hg t)
    apply hd.congr_deriv
    ring
  have hFd : DifferentiableOn ℝ F univ :=
    fun t _ => (hF t).differentiableAt.differentiableWithinAt
  have hGd : DifferentiableOn ℝ (fun _ : ℝ => g 0) univ :=
    fun t _ => (hasDerivAt_const t (g 0)).differentiableAt.differentiableWithinAt
  have hder : EqOn (deriv F) (deriv (fun _ : ℝ => g 0)) univ := by
    intro t _
    exact (hF t).deriv.trans (hasDerivAt_const t (g 0)).deriv.symm
  have hinit : F 0 = g 0 := by simp only [F, P, intervalIntegral.integral_same,
    neg_zero, Complex.exp_zero, one_mul]
  have hconst : EqOn F (fun _ : ℝ => g 0) univ :=
    isOpen_univ.eqOn_of_deriv_eq isPreconnected_univ hFd hGd hder (mem_univ 0) hinit
  have hprod : Complex.exp (-P T) * g 0 = g 0 := by
    simpa only [F, hclosed] using hconst (mem_univ T)
  have hneg : Complex.exp (-P T) = 1 := by
    apply mul_right_cancel₀ h0
    simpa only [one_mul] using hprod
  refine ⟨hi T, ?_⟩
  change Complex.exp (P T) = 1
  simpa only [Complex.exp_neg, inv_eq_one] using hneg

theorem closedLogarithmicODETarget : ClosedLogarithmicODETarget :=
  exp_integral_eq_one_of_closed_logarithmic_ODE

end NlsGge.Analysis.NonvanishingLoop
