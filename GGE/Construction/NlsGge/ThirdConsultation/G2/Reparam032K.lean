import Mathlib
import NlsGge.ThirdConsultation.G2.Reparam032F

                                                                                                             
                                                                                                    
                                                                                   
                                                                                                    
set_option autoImplicit false
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G2032Ellipse
noncomputable section

/-- Derivative of `t ↦ z(t) = (q/p) e^{−2it}`. -/
theorem hasDerivAt_ellZ (p q : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ellZ p q s) (-(2 * Complex.I) * ellZ p q t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => -(2 * (s : ℂ) * Complex.I)) (-(2 * 1 * Complex.I)) t :=
    ((h1.const_mul 2).mul_const Complex.I).neg
  have h3 := (h2.cexp).const_mul (q / p)
  unfold ellZ
  convert h3 using 1
  ring

/-- Closed form: `1 + Im(−2i z/(1+z)) = (1 − z.re² − z.im²)/((1+z.re)² + z.im²)`, positive for `‖z‖ < 1`. -/
theorem one_add_im_pos (z : ℂ) (hz : ‖z‖ < 1) :
    0 < 1 + (-(2 * Complex.I) * z / (1 + z)).im := by
  have hsq : z.re ^ 2 + z.im ^ 2 < 1 := by
    have h1 : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [h1]
    nlinarith [norm_nonneg z]
  have ha : -1 < z.re := by nlinarith [sq_nonneg z.im]
  have hN : 0 < (1 + z.re) * (1 + z.re) + z.im * z.im := by
    nlinarith [sq_nonneg z.im, mul_pos (show (0 : ℝ) < 1 + z.re by linarith)
      (show (0 : ℝ) < 1 + z.re by linarith)]
  have hx_re : (-(2 * Complex.I) * z).re = 2 * z.im := by simp
  have hx_im : (-(2 * Complex.I) * z).im = -2 * z.re := by simp
  have key : (-(2 * Complex.I) * z / (1 + z)).im =
      (-2 * z.re * (1 + z.re) - 2 * z.im * z.im) / ((1 + z.re) * (1 + z.re) + z.im * z.im) := by
    rw [Complex.div_im, hx_re, hx_im, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add]
    rw [div_sub_div_same]
  rw [key, one_add_div hN.ne']
  apply div_pos _ hN
  nlinarith [hsq]

/-- The derivative of the explicit ellipse angle. -/
theorem hasDerivAt_ellArg (p q : ℂ) (hpq : ‖q‖ < ‖p‖) (t : ℝ) :
    HasDerivAt (ellArg p q) (1 + (-(2 * Complex.I) * ellZ p q t / (1 + ellZ p q t)).im) t := by
  have hL : HasDerivAt (fun s : ℝ => Complex.log (1 + ellZ p q s))
      (-(2 * Complex.I) * ellZ p q t / (1 + ellZ p q t)) t :=
    ((hasDerivAt_ellZ p q t).const_add 1).clog_real (one_add_ellZ_mem_slitPlane p q hpq t)
  have him : HasDerivAt (fun s : ℝ => (Complex.log (1 + ellZ p q s)).im)
      (-(2 * Complex.I) * ellZ p q t / (1 + ellZ p q t)).im t := by
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hL
  have h := ((hasDerivAt_id t).const_add (Complex.arg p)).add him
  have hfun : ellArg p q = fun s => (Complex.arg p + s) + (Complex.log (1 + ellZ p q s)).im := rfl
  rw [hfun]
  exact h

/-- The explicit ellipse ray angle is strictly increasing. -/
theorem ellArg_strictMono (p q : ℂ) (hpq : ‖q‖ < ‖p‖) : StrictMono (ellArg p q) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_ellArg p q hpq x).deriv]
  exact one_add_im_pos (ellZ p q x) (norm_ellZ_lt p q hpq x)

/-- Selftest: the hypotheses are satisfiable (p = 1, q = 0), so the conclusion is not vacuous. -/
example : StrictMono (ellArg 1 0) := ellArg_strictMono 1 0 (by simp)

end
end G2032Ellipse
end NlsGge.GKDefinitionDesign

