import Mathlib

                                                                                                                    
                                                                                                    
                                                                               
                                                 
                                                                                             
                                                           
set_option autoImplicit false
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G2032Ellipse
noncomputable section

/-- The ellipse `f(t) = p e^{it} + q e^{-it}`. -/
def ellF (p q : ℂ) (t : ℝ) : ℂ :=
  p * Complex.exp ((t : ℂ) * Complex.I) + q * Complex.exp (-((t : ℂ) * Complex.I))

/-- The auxiliary factor `z(t) = (q/p) e^{-2it}`. -/
def ellZ (p q : ℂ) (t : ℝ) : ℂ :=
  (q / p) * Complex.exp (-(2 * (t : ℂ) * Complex.I))

/-- The explicit lifted angle `arg p + t + Im Log(1 + z(t))`. -/
def ellArg (p q : ℂ) (t : ℝ) : ℝ :=
  Complex.arg p + t + (Complex.log (1 + ellZ p q t)).im

theorem norm_exp_neg_two (t : ℝ) :
    ‖Complex.exp (-(2 * (t : ℂ) * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem p_ne_zero_of_lt (p q : ℂ) (hpq : ‖q‖ < ‖p‖) : p ≠ 0 := by
  intro h
  rw [h, norm_zero] at hpq
  exact absurd hpq (not_lt.mpr (norm_nonneg q))

theorem norm_ellZ_lt (p q : ℂ) (hpq : ‖q‖ < ‖p‖) (t : ℝ) : ‖ellZ p q t‖ < 1 := by
  unfold ellZ
  rw [norm_mul, norm_exp_neg_two, mul_one, norm_div]
  exact (div_lt_one (norm_pos_iff.mpr (p_ne_zero_of_lt p q hpq))).mpr hpq

theorem one_add_ellZ_re_pos (p q : ℂ) (hpq : ‖q‖ < ‖p‖) (t : ℝ) :
    0 < (1 + ellZ p q t).re := by
  have h1 := norm_ellZ_lt p q hpq t
  have h2 := Complex.abs_re_le_norm (ellZ p q t)
  have h3 := neg_abs_le (ellZ p q t).re
  rw [Complex.add_re, Complex.one_re]
  linarith

theorem one_add_ellZ_mem_slitPlane (p q : ℂ) (hpq : ‖q‖ < ‖p‖) (t : ℝ) :
    1 + ellZ p q t ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (one_add_ellZ_re_pos p q hpq t))

theorem one_add_ellZ_ne_zero (p q : ℂ) (hpq : ‖q‖ < ‖p‖) (t : ℝ) :
    1 + ellZ p q t ≠ 0 :=
  Complex.slitPlane_ne_zero (one_add_ellZ_mem_slitPlane p q hpq t)

/-- Factorization `f(t) = p e^{it} (1 + z(t))`. -/
theorem ellF_eq_factor (p q : ℂ) (hp : p ≠ 0) (t : ℝ) :
    ellF p q t = p * Complex.exp ((t : ℂ) * Complex.I) * (1 + ellZ p q t) := by
  unfold ellF ellZ
  have h1 : Complex.exp ((t : ℂ) * Complex.I) * Complex.exp (-(2 * (t : ℂ) * Complex.I)) =
      Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have h2 : p * (q / p) = q := by
    field_simp
  linear_combination (-(Complex.exp ((t : ℂ) * Complex.I) *
    Complex.exp (-(2 * (t : ℂ) * Complex.I)))) * h2 + (-q) * h1

/-- Polar identity for a product `p e^{it} w`. -/
theorem polar_identity (p w : ℂ) (t : ℝ) :
    p * Complex.exp ((t : ℂ) * Complex.I) * w =
      (((‖p‖ * ‖w‖ : ℝ) : ℂ)) *
        Complex.exp (((Complex.arg p + t + Complex.arg w : ℝ) : ℂ) * Complex.I) := by
  have hp := Complex.norm_mul_exp_arg_mul_I p
  have hw := Complex.norm_mul_exp_arg_mul_I w
  conv_lhs => rw [← hp, ← hw]
  rw [show (((Complex.arg p + t + Complex.arg w : ℝ) : ℂ)) * Complex.I =
      (Complex.arg p : ℂ) * Complex.I + (t : ℂ) * Complex.I + (Complex.arg w : ℂ) * Complex.I by
    push_cast
    ring, Complex.exp_add, Complex.exp_add]
  push_cast
  ring

theorem norm_ellF_eq (p q : ℂ) (hpq : ‖q‖ < ‖p‖) (t : ℝ) :
    ‖ellF p q t‖ = ‖p‖ * ‖1 + ellZ p q t‖ := by
  rw [ellF_eq_factor p q (p_ne_zero_of_lt p q hpq) t, norm_mul, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem ellArg_eq (p q : ℂ) (t : ℝ) :
    ellArg p q t = Complex.arg p + t + Complex.arg (1 + ellZ p q t) := by
  unfold ellArg
  rw [Complex.log_im]

/-- The explicit lift: `f(t) = ‖f(t)‖ exp(i·ellArg t)`. -/
theorem ellF_eq_norm_mul_exp (p q : ℂ) (hpq : ‖q‖ < ‖p‖) (t : ℝ) :
    ellF p q t = ((‖ellF p q t‖ : ℝ) : ℂ) * Complex.exp ((ellArg p q t : ℂ) * Complex.I) := by
  calc ellF p q t = p * Complex.exp ((t : ℂ) * Complex.I) * (1 + ellZ p q t) :=
        ellF_eq_factor p q (p_ne_zero_of_lt p q hpq) t
    _ = (((‖p‖ * ‖1 + ellZ p q t‖ : ℝ)) : ℂ) *
          Complex.exp (((Complex.arg p + t + Complex.arg (1 + ellZ p q t) : ℝ) : ℂ) * Complex.I) :=
        polar_identity p (1 + ellZ p q t) t
    _ = _ := by
        rw [← norm_ellF_eq p q hpq t, ← ellArg_eq p q t]

/-- Periodicity of the exponential factor: `e^{-2i(t+2π)} = e^{-2it}`. -/
theorem exp_neg_two_add_two_pi (t : ℝ) :
    Complex.exp (-(2 * ((t + 2 * π : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(2 * (t : ℂ) * Complex.I)) := by
  rw [show -(2 * ((t + 2 * π : ℝ) : ℂ) * Complex.I) =
      -(2 * (t : ℂ) * Complex.I) + ((-2 : ℤ) : ℂ) * (2 * (π : ℂ) * Complex.I) by
    push_cast
    ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The lift is 2π-equivariant: `ellArg(t + 2π) = ellArg t + 2π`. -/
theorem ellArg_add_two_pi (p q : ℂ) (t : ℝ) :
    ellArg p q (t + 2 * π) = ellArg p q t + 2 * π := by
  unfold ellArg ellZ
  rw [exp_neg_two_add_two_pi t]
  ring

/-- Smoothness of the explicit lift (C²,  on the real line). -/
theorem ellArg_contDiff (p q : ℂ) (hpq : ‖q‖ < ‖p‖) : ContDiff ℝ 2 (ellArg p q) := by
  have hofR : ContDiff ℝ 2 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hcoef : ContDiff ℝ 2 (fun t : ℝ => -(2 * (t : ℂ) * Complex.I)) :=
    ((contDiff_const.mul hofR).mul contDiff_const).neg
  have hexp : ContDiff ℝ 2 (fun t : ℝ => Complex.exp (-(2 * (t : ℂ) * Complex.I))) :=
    Complex.contDiff_exp.comp hcoef
  have hz : ContDiff ℝ 2 (fun t : ℝ => 1 + ellZ p q t) := by
    unfold ellZ
    exact contDiff_const.add (contDiff_const.mul hexp)
  have hlog : ContDiff ℝ 2 (fun t : ℝ => Complex.log (1 + ellZ p q t)) := by
    refine contDiff_iff_contDiffAt.mpr fun t => ?_
    have hzA : ContDiffAt ℝ 2 (fun t : ℝ => 1 + ellZ p q t) t := hz.contDiffAt
    have hL : ContDiffAt ℝ 2 Complex.log (1 + ellZ p q t) :=
      ContDiffAt.restrict_scalars (𝕜 := ℝ)
        (Complex.contDiffAt_log (one_add_ellZ_mem_slitPlane p q hpq t) (n := 2))
    exact ContDiffAt.comp t hL hzA
  have him : ContDiff ℝ 2 (fun t : ℝ => (Complex.log (1 + ellZ p q t)).im) :=
    Complex.imCLM.contDiff.comp hlog
  unfold ellArg
  exact (contDiff_const.add contDiff_id).add him

/-- Selftest: the lift identity and periodicity at a sample point. -/
example (t : ℝ) : ellArg 1 0 (t + 2 * π) = ellArg 1 0 t + 2 * π :=
  ellArg_add_two_pi 1 0 t

end
end G2032Ellipse
end NlsGge.GKDefinitionDesign

