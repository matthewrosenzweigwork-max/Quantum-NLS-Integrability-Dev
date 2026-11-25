import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Weighted real-axis ODE invariant

SPECULATIVE_PARENT_UNACCEPTED, RT-ODE-012. These two ordinary infrastructure
lemmas isolate a real derivative invariant and its complex restriction. They
prove only the weighted product vanishes. Coefficient reality at a zero of Q
is not asserted. The real neighborhood is open and preconnected; later actual
consumers use the original filled-disc real slice, including repeated gaps
and terminal tips. Source beta/correction reality remains separate work.
-/
set_option autoImplicit false
open Set
namespace NlsGge.GK38
noncomputable section

/-- The squared weighted imaginary component is constant and anchored at zero. -/
theorem gk_real_weighted_ode_invariant38
    (U : Set ℝ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (p y : ℝ → ℝ)
    (hp : ∀ t ∈ U, DifferentiableAt ℝ p t)
    (hy : ∀ t ∈ U, DifferentiableAt ℝ y t)
    (hODE : ∀ t ∈ U,
      p t * deriv y t + (deriv p t / 2) * y t = 0)
    (a x : ℝ) (ha : a ∈ U) (hx : x ∈ U) (hpa : p a = 0) :
    p x * (y x)^2 = 0 := by
  let J : ℝ → ℝ := fun t => p t * (y t)^2
  have hJ : DifferentiableOn ℝ J U := by
    intro t ht
    exact ((hp t ht).mul ((hy t ht).pow 2)).differentiableWithinAt
  have hJderiv : U.EqOn (deriv J) 0 := by
    intro t ht
    have hd : HasDerivAt J
        (deriv p t * (y t)^2 + p t * (2*y t*deriv y t)) t := by
      apply ((hp t ht).hasDerivAt.mul ((hy t ht).hasDerivAt.pow 2)).congr_deriv
      change deriv p t * (y t)^2 +
        p t * (2*(y t)^(2-1)*deriv y t) = _
      ring
    change deriv J t = 0
    rw [hd.deriv]
    linear_combination 2*y t*(hODE t ht)
  have hconst : J x = J a :=
    hU.is_const_of_deriv_eq_zero hUc hJ hJderiv hx ha
  simpa only [J,hpa,zero_mul] using hconst

/-- Restrict the actual complex ODE to its open real neighborhood before
applying the scalar invariant. No gap or characteristic division occurs. -/
theorem gk_real_axis_weighted_ode_invariant38
    (U : Set ℝ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (Q R Psi : ℂ → ℂ)
    (hQ : ∀ x ∈ U, DifferentiableAt ℂ Q (x : ℂ))
    (hR : ∀ x ∈ U, DifferentiableAt ℂ R (x : ℂ))
    (hQreal : ∀ x ∈ U, (Q (x : ℂ)).im = 0)
    (hPsireal : ∀ x ∈ U, (Psi (x : ℂ)).im = 0)
    (hODE : ∀ x ∈ U,
      Q (x : ℂ)*deriv R (x : ℂ) +
        (deriv Q (x : ℂ)/2)*R (x : ℂ) = Psi (x : ℂ))
    (a x : ℝ) (ha : a ∈ U) (hx : x ∈ U) (hQa : Q (a : ℂ) = 0) :
    (Q (x : ℂ)).re * ((R (x : ℂ)).im)^2 = 0 := by
  let p : ℝ → ℝ := fun t => (Q (t : ℂ)).re
  let y : ℝ → ℝ := fun t => (R (t : ℂ)).im
  have hpd : ∀ t ∈ U,
      HasDerivAt p (deriv Q (t : ℂ)).re t := by
    intro t ht
    exact (hQ t ht).hasDerivAt.real_of_complex
  have hyd : ∀ t ∈ U,
      HasDerivAt y (deriv R (t : ℂ)).im t := by
    intro t ht
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      (hR t ht).hasDerivAt.comp_ofReal
  have hQderivReal : ∀ t ∈ U, (deriv Q (t : ℂ)).im = 0 := by
    intro t ht
    have hi : HasDerivAt
        (fun s : ℝ => (Q (s : ℂ)).im) (deriv Q (t : ℂ)).im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
        (hQ t ht).hasDerivAt.comp_ofReal
    have heq : U.EqOn (fun s : ℝ => (Q (s : ℂ)).im)
        (fun _s : ℝ => (0 : ℝ)) := by
      intro s hs
      exact hQreal s hs
    have hz : deriv (fun s : ℝ => (Q (s : ℂ)).im) t = 0 := by
      simpa only [deriv_const] using (heq.deriv hU ht)
    exact hi.deriv.symm.trans hz
  have hscalar : ∀ t ∈ U,
      p t * deriv y t + (deriv p t / 2) * y t = 0 := by
    intro t ht
    change (Q (t : ℂ)).re * deriv y t +
      (deriv p t / 2) * (R (t : ℂ)).im = 0
    rw [(hyd t ht).deriv, (hpd t ht).deriv]
    have him := congrArg Complex.im (hODE t ht)
    simpa only [Complex.add_im,Complex.mul_im,Complex.div_ofNat_re,
      Complex.div_ofNat_im,hQreal t ht,hQderivReal t ht,hPsireal t ht,
      zero_mul,zero_div,mul_zero,add_zero] using him
  have hpa : p a = 0 := by
    change (Q (a : ℂ)).re = 0
    rw [hQa,Complex.zero_re]
  change p x * (y x)^2 = 0
  exact gk_real_weighted_ode_invariant38 U hU hUc p y
    (fun t ht => (hpd t ht).differentiableAt)
    (fun t ht => (hyd t ht).differentiableAt) hscalar a x ha hx hpa

end
end NlsGge.GK38
