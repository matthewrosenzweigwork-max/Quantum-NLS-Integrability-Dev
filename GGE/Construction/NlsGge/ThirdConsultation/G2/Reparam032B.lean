import Mathlib

                                                                                               
                                                                                              
                                                                                             
                                                                                               
                                         
set_option autoImplicit false

open MeasureTheory Metric
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G2032Lift
noncomputable section

/-- The isolating circle `θ ↦ w + R e^{iθ}`. -/
def liftF (w : ℂ) (R : ℝ) (θ : ℝ) : ℂ := w + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

/-- Real and imaginary parts of the circle, and their derivatives. -/
def liftX (w : ℂ) (R : ℝ) (θ : ℝ) : ℝ := w.re + R * Real.cos θ
def liftY (w : ℂ) (R : ℝ) (θ : ℝ) : ℝ := w.im + R * Real.sin θ
def liftDX (R : ℝ) (θ : ℝ) : ℝ := R * -Real.sin θ
def liftDY (R : ℝ) (θ : ℝ) : ℝ := R * Real.cos θ

/-- `P = X X' + Y Y'`, which is half the derivative of `|f|²`. -/
def liftP (w : ℂ) (R : ℝ) (θ : ℝ) : ℝ := liftX w R θ * liftDX R θ + liftY w R θ * liftDY R θ

/-- The angle rate `R (R + Re(e^{iθ} conj w)) / |f(θ)|²`. -/
def liftRate (w : ℂ) (R : ℝ) (θ : ℝ) : ℝ :=
  R * (R + (Complex.exp ((θ : ℂ) * Complex.I) * (starRingEnd ℂ) w).re) /
    Complex.normSq (liftF w R θ)

/-- The lifted angle, normalized so that `liftAngle 0 = arg f(0)`. -/
def liftAngle (w : ℂ) (R : ℝ) (θ : ℝ) : ℝ :=
  Complex.arg (liftF w R 0) + ∫ s in (0 : ℝ)..θ, liftRate w R s

/-- The modulus written as `√|f|²`, so that `HasDerivAt.sqrt` applies. -/
def liftRho (w : ℂ) (R : ℝ) (θ : ℝ) : ℝ := Real.sqrt (Complex.normSq (liftF w R θ))

/-- The auxiliary unit-modulus quotient whose constancy gives the lift. -/
def liftG (w : ℂ) (R : ℝ) (θ : ℝ) : ℂ :=
  liftF w R θ * Complex.exp (-(Complex.I * ((liftAngle w R θ : ℝ) : ℂ))) /
    ((liftRho w R θ : ℝ) : ℂ)

theorem liftF_continuous (w : ℂ) (R : ℝ) : Continuous (fun θ : ℝ => liftF w R θ) := by
  unfold liftF; fun_prop

theorem liftF_re (w : ℂ) (R : ℝ) (θ : ℝ) : (liftF w R θ).re = liftX w R θ := by
  simp only [liftF, liftX, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]

theorem liftF_im (w : ℂ) (R : ℝ) (θ : ℝ) : (liftF w R θ).im = liftY w R θ := by
  simp only [liftF, liftY, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]

theorem normSq_liftF (w : ℂ) (R : ℝ) (θ : ℝ) :
    Complex.normSq (liftF w R θ) = liftX w R θ * liftX w R θ + liftY w R θ * liftY w R θ := by
  rw [Complex.normSq_apply, liftF_re, liftF_im]

theorem liftF_norm_pos (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) (θ : ℝ) :
    0 < ‖liftF w R θ‖ := by
  have h1 : liftF w R θ - w = (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    unfold liftF; ring
  have h2 : ‖(R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = R := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hR.le]
  have h3 := norm_sub_le (liftF w R θ) w
  rw [h1, h2] at h3
  linarith

theorem normSq_liftF_pos (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) (θ : ℝ) :
    0 < Complex.normSq (liftF w R θ) := by
  rw [Complex.normSq_eq_norm_sq]; exact pow_pos (liftF_norm_pos w R hR hw θ) 2

theorem liftRho_eq_norm (w : ℂ) (R : ℝ) (θ : ℝ) : liftRho w R θ = ‖liftF w R θ‖ := by
  unfold liftRho; rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem liftRate_continuous (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) :
    Continuous (liftRate w R) := by
  have hnum : Continuous (fun θ : ℝ =>
      R * (R + (Complex.exp ((θ : ℂ) * Complex.I) * (starRingEnd ℂ) w).re)) := by
    fun_prop
  unfold liftRate
  exact hnum.div (Complex.continuous_normSq.comp (liftF_continuous w R))
    (fun θ => (normSq_liftF_pos w R hR hw θ).ne')

theorem liftQ_continuous (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) :
    Continuous (fun θ : ℝ => liftP w R θ / Complex.normSq (liftF w R θ)) := by
  have hP : Continuous (fun θ : ℝ => liftP w R θ) := by
    unfold liftP liftX liftY liftDX liftDY; fun_prop
  exact hP.div (Complex.continuous_normSq.comp (liftF_continuous w R))
    (fun θ => (normSq_liftF_pos w R hR hw θ).ne')

theorem hasDerivAt_liftF (w : ℂ) (R : ℝ) (θ : ℝ) :
    HasDerivAt (liftF w R) ((R : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I)) θ := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp
  have key := ((((h1.mul_const Complex.I).cexp).const_mul (R : ℂ)).const_add w :
    HasDerivAt (fun y : ℝ => w + (R : ℂ) * Complex.exp ((y : ℂ) * Complex.I))
      ((R : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * (1 * Complex.I))) θ)
  rw [one_mul] at key
  exact key

theorem hasDerivAt_liftX (w : ℂ) (R : ℝ) (θ : ℝ) : HasDerivAt (liftX w R) (liftDX R θ) θ :=
  ((Real.hasDerivAt_cos θ).const_mul R).const_add w.re

theorem hasDerivAt_liftY (w : ℂ) (R : ℝ) (θ : ℝ) : HasDerivAt (liftY w R) (liftDY R θ) θ :=
  ((Real.hasDerivAt_sin θ).const_mul R).const_add w.im

theorem hasDerivAt_normSq_liftF (w : ℂ) (R : ℝ) (θ : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.normSq (liftF w R y)) (2 * liftP w R θ) θ := by
  have hfun : (fun y : ℝ => Complex.normSq (liftF w R y)) =
      fun y : ℝ => liftX w R y * liftX w R y + liftY w R y * liftY w R y :=
    funext fun y => normSq_liftF w R y
  rw [hfun]
  have h := ((hasDerivAt_liftX w R θ).mul (hasDerivAt_liftX w R θ)).add
    ((hasDerivAt_liftY w R θ).mul (hasDerivAt_liftY w R θ))
  convert h using 1
  unfold liftP; ring

theorem hasDerivAt_liftRho (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) (θ : ℝ) :
    HasDerivAt (liftRho w R) (liftP w R θ / liftRho w R θ) θ := by
  have h := (hasDerivAt_normSq_liftF w R θ).sqrt (normSq_liftF_pos w R hR hw θ).ne'
  have e : liftP w R θ / liftRho w R θ =
      2 * liftP w R θ / (2 * Real.sqrt (Complex.normSq (liftF w R θ))) := by
    unfold liftRho; ring
  rw [e]
  exact h

theorem hasDerivAt_liftAngle (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) (θ : ℝ) :
    HasDerivAt (liftAngle w R) (liftRate w R θ) θ :=
  ((liftRate_continuous w R hR hw).integral_hasStrictDerivAt 0 θ).hasDerivAt.const_add
    (Complex.arg (liftF w R 0))

theorem liftRate_mul_normSq (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) (θ : ℝ) :
    liftRate w R θ * Complex.normSq (liftF w R θ) =
      liftX w R θ * liftDY R θ - liftY w R θ * liftDX R θ := by
  have hN := (normSq_liftF_pos w R hR hw θ).ne'
  have hre : (Complex.exp ((θ : ℂ) * Complex.I) * (starRingEnd ℂ) w).re =
      Real.cos θ * w.re + Real.sin θ * w.im := by
    simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have hsc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  unfold liftRate
  rw [div_mul_cancel₀ _ hN, hre]
  simp only [liftX, liftY, liftDX, liftDY]
  linear_combination (-R ^ 2) * hsc

theorem real_core (X Y dX dY q A N : ℝ) (hN : N ≠ 0) (hNdef : N = X * X + Y * Y)
    (hq : q * N = X * dX + Y * dY) (hA : A * N = X * dY - Y * dX) :
    X * q - Y * A = dX ∧ X * A + Y * q = dY := by
  refine ⟨mul_right_cancel₀ hN ?_, mul_right_cancel₀ hN ?_⟩
  · linear_combination X * hq - Y * hA - dX * hNdef
  · linear_combination X * hA + Y * hq - dY * hNdef

theorem liftF_deriv_eq (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) (θ : ℝ) :
    (R : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) =
      liftF w R θ * (Complex.I * ((liftRate w R θ : ℝ) : ℂ) +
        ((liftP w R θ / Complex.normSq (liftF w R θ) : ℝ) : ℂ)) := by
  have hN := (normSq_liftF_pos w R hR hw θ).ne'
  have hq : liftP w R θ / Complex.normSq (liftF w R θ) * Complex.normSq (liftF w R θ) =
      liftP w R θ := div_mul_cancel₀ _ hN
  obtain ⟨h1, h2⟩ := real_core (liftX w R θ) (liftY w R θ) (liftDX R θ) (liftDY R θ)
    (liftP w R θ / Complex.normSq (liftF w R θ)) (liftRate w R θ) (Complex.normSq (liftF w R θ))
    hN (normSq_liftF w R θ) hq (liftRate_mul_normSq w R hR hw θ)
  simp only [liftDX, liftDY, liftX, liftY] at h1 h2
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, liftF_re, liftF_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp only [liftX, liftY]
    linear_combination (-1 : ℝ) * h1
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, liftF_re, liftF_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp only [liftX, liftY]
    linear_combination (-1 : ℝ) * h2

theorem alg_core (F F' E A P N ρ d' : ℂ) (hF' : F' = F * (Complex.I * A + P / N))
    (hd' : d' = P / ρ) (hN : N ≠ 0) (hρ : ρ ≠ 0) (hsq : ρ * ρ = N) :
    (F' * E + F * (E * (-(Complex.I * A)))) * ρ - F * E * d' = 0 := by
  subst hF' hd' hsq
  field_simp
  ring

theorem hasDerivAt_liftG (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) (θ : ℝ) :
    HasDerivAt (liftG w R) 0 θ := by
  have hF := hasDerivAt_liftF w R θ
  have hE := (((hasDerivAt_liftAngle w R hR hw θ).ofReal_comp.const_mul Complex.I).neg).cexp
  have hρ := (hasDerivAt_liftRho w R hR hw θ).ofReal_comp
  have hρpos : 0 < liftRho w R θ := Real.sqrt_pos.2 (normSq_liftF_pos w R hR hw θ)
  have hρne : ((liftRho w R θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρpos.ne'
  have hN : ((Complex.normSq (liftF w R θ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (normSq_liftF_pos w R hR hw θ).ne'
  have hsqR : liftRho w R θ * liftRho w R θ = Complex.normSq (liftF w R θ) :=
    Real.mul_self_sqrt (Complex.normSq_nonneg _)
  have hsq : ((liftRho w R θ : ℝ) : ℂ) * ((liftRho w R θ : ℝ) : ℂ) =
      ((Complex.normSq (liftF w R θ) : ℝ) : ℂ) := by
    exact_mod_cast hsqR
  have hF' : (R : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) =
      liftF w R θ * (Complex.I * ((liftRate w R θ : ℝ) : ℂ) +
        ((liftP w R θ : ℝ) : ℂ) / ((Complex.normSq (liftF w R θ) : ℝ) : ℂ)) := by
    rw [liftF_deriv_eq w R hR hw θ, Complex.ofReal_div]
  have hd' : ((liftP w R θ / liftRho w R θ : ℝ) : ℂ) =
      ((liftP w R θ : ℝ) : ℂ) / ((liftRho w R θ : ℝ) : ℂ) := Complex.ofReal_div _ _
  have hq := (hF.mul hE).div hρ hρne
  refine HasDerivAt.congr_deriv hq ?_
  rw [div_eq_zero_iff]
  left
  exact alg_core _ _ _ _ _ _ _ _ hF' hd' hN hρne hsq

theorem liftG_zero (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) : liftG w R 0 = 1 := by
  have hang : liftAngle w R 0 = Complex.arg (liftF w R 0) := by
    unfold liftAngle; rw [intervalIntegral.integral_same, add_zero]
  have hpos : (‖liftF w R 0‖ : ℂ) ≠ 0 := by exact_mod_cast (liftF_norm_pos w R hR hw 0).ne'
  have hpolar := Complex.norm_mul_exp_arg_mul_I (liftF w R 0)
  have hexp : Complex.exp ((Complex.arg (liftF w R 0) : ℂ) * Complex.I) *
      Complex.exp (-(Complex.I * ((Complex.arg (liftF w R 0) : ℝ) : ℂ))) = 1 := by
    rw [← Complex.exp_add, show (Complex.arg (liftF w R 0) : ℂ) * Complex.I +
      -(Complex.I * ((Complex.arg (liftF w R 0) : ℝ) : ℂ)) = 0 by ring, Complex.exp_zero]
  unfold liftG
  rw [hang, liftRho_eq_norm, div_eq_one_iff_eq hpos]
  calc _ = (((‖liftF w R 0‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg (liftF w R 0) : ℂ) * Complex.I)) *
        Complex.exp (-(Complex.I * ((Complex.arg (liftF w R 0) : ℝ) : ℂ))) := by rw [hpolar]
    _ = ((‖liftF w R 0‖ : ℝ) : ℂ) * (Complex.exp ((Complex.arg (liftF w R 0) : ℂ) * Complex.I) *
        Complex.exp (-(Complex.I * ((Complex.arg (liftF w R 0) : ℝ) : ℂ)))) := mul_assoc _ _ _
    _ = ((‖liftF w R 0‖ : ℝ) : ℂ) := by rw [hexp, mul_one]

theorem liftRate_periodic (w : ℂ) (R : ℝ) (θ : ℝ) :
    liftRate w R (θ + 2 * π) = liftRate w R θ := by
  have hexp : Complex.exp (((θ + 2 * π : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [(by push_cast; ring : ((θ + 2 * π : ℝ) : ℂ) * Complex.I =
      (θ : ℂ) * Complex.I + 2 * π * Complex.I), Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  unfold liftRate liftF
  rw [hexp]

theorem liftRate_integral (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) :
    ∫ s in (0 : ℝ)..(2 * π), liftRate w R s = 2 * π := by
  have hmem : (0 : ℂ) ∈ Metric.ball w R := by
    rw [Metric.mem_ball, dist_comm, dist_zero_right]; exact hw
  have hcirc : circleIntegral (fun z : ℂ => (z - 0)⁻¹) w R = 2 * π * Complex.I :=
    circleIntegral.integral_sub_inv_of_mem_ball hmem
  have hinv : ∀ F Y : ℂ, F ≠ 0 → F * Y * F⁻¹ = Y := fun F Y hF => by
    rw [mul_assoc, mul_comm Y, ← mul_assoc, mul_inv_cancel₀ hF, one_mul]
  have hpt : ∀ θ : ℝ, deriv (circleMap w R) θ • (circleMap w R θ - 0)⁻¹ =
      ((liftP w R θ / Complex.normSq (liftF w R θ) : ℝ) : ℂ) +
        Complex.I * ((liftRate w R θ : ℝ) : ℂ) := by
    intro θ
    have hF0 : liftF w R θ ≠ 0 := norm_pos_iff.mp (liftF_norm_pos w R hR hw θ)
    have hd : deriv (circleMap w R) θ =
        (R : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) := by
      rw [deriv_circleMap, circleMap_zero, mul_assoc]
    have hc : circleMap w R θ = liftF w R θ := rfl
    rw [hd, hc, sub_zero, smul_eq_mul, liftF_deriv_eq w R hR hw θ, hinv _ _ hF0]
    ring
  have hcirc' : ∫ θ in (0 : ℝ)..(2 * π),
      (((liftP w R θ / Complex.normSq (liftF w R θ) : ℝ) : ℂ) +
        Complex.I * ((liftRate w R θ : ℝ) : ℂ)) = 2 * π * Complex.I := by
    rw [← hcirc]
    unfold circleIntegral
    exact intervalIntegral.integral_congr (fun θ _ => (hpt θ).symm)
  have hq_c := liftQ_continuous w R hR hw
  have hA_c := liftRate_continuous w R hR hw
  have h1 : IntervalIntegrable
      (fun θ : ℝ => ((liftP w R θ / Complex.normSq (liftF w R θ) : ℝ) : ℂ))
      MeasureTheory.volume 0 (2 * π) :=
    (Complex.continuous_ofReal.comp hq_c).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ : ℝ => Complex.I * ((liftRate w R θ : ℝ) : ℂ))
      MeasureTheory.volume 0 (2 * π) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hA_c)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal] at hcirc'
  have him := congrArg Complex.im hcirc'
  simpa using him

theorem liftAngle_periodic (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) (θ : ℝ) :
    liftAngle w R (θ + 2 * π) = liftAngle w R θ + 2 * π := by
  have hD : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => liftAngle w R (y + 2 * π) - liftAngle w R y) 0 x := by
    intro x
    have h1 := HasDerivAt.comp_add_const x (2 * π) (hasDerivAt_liftAngle w R hR hw (x + 2 * π))
    have h3 := h1.sub (hasDerivAt_liftAngle w R hR hw x)
    rw [liftRate_periodic, sub_self] at h3
    exact h3
  have hC : ∀ x : ℝ, liftAngle w R (x + 2 * π) - liftAngle w R x =
      liftAngle w R (0 + 2 * π) - liftAngle w R 0 := fun x =>
    is_const_of_deriv_eq_zero (f := fun y : ℝ => liftAngle w R (y + 2 * π) - liftAngle w R y)
      (fun z => (hD z).differentiableAt) (fun z => (hD z).deriv) x 0
  have h0 : liftAngle w R (0 + 2 * π) - liftAngle w R 0 = 2 * π := by
    rw [zero_add]; unfold liftAngle
    rw [intervalIntegral.integral_same, liftRate_integral w R hR hw]; ring
  linarith [hC θ, h0]

theorem hasDerivAt_liftG_const (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) (θ : ℝ) :
    liftG w R θ = liftG w R 0 :=
  is_const_of_deriv_eq_zero (f := liftG w R)
    (fun x => (hasDerivAt_liftG w R hR hw x).differentiableAt)
    (fun x => (hasDerivAt_liftG w R hR hw x).deriv) θ 0

/-- LIFT032: ray-angle lift of the isolating circle `θ ↦ w + R e^{iθ}`, `|w| < R`. -/
theorem lift_circle (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) :
    ∃ α : ℝ → ℝ,
      (∀ θ : ℝ, HasDerivAt α (liftRate w R θ) θ) ∧
      (∀ θ : ℝ, liftF w R θ / ((‖liftF w R θ‖ : ℝ) : ℂ) =
        Complex.exp (((α θ : ℝ) : ℂ) * Complex.I)) ∧
      (∀ θ : ℝ, α (θ + 2 * π) = α θ + 2 * π) := by
  refine ⟨liftAngle w R, fun θ => hasDerivAt_liftAngle w R hR hw θ, ?_,
    fun θ => liftAngle_periodic w R hR hw θ⟩
  intro θ
  have hG1 : liftG w R θ = 1 := (hasDerivAt_liftG_const w R hR hw θ).trans (liftG_zero w R hR hw)
  have hρpos : 0 < liftRho w R θ := Real.sqrt_pos.2 (normSq_liftF_pos w R hR hw θ)
  have hρne : ((liftRho w R θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρpos.ne'
  unfold liftG at hG1
  rw [div_eq_one_iff_eq hρne] at hG1
  have hinv : Complex.exp (-(Complex.I * ((liftAngle w R θ : ℝ) : ℂ))) *
      Complex.exp (((liftAngle w R θ : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, show -(Complex.I * ((liftAngle w R θ : ℝ) : ℂ)) +
      ((liftAngle w R θ : ℝ) : ℂ) * Complex.I = 0 by ring, Complex.exp_zero]
  have hFeq : liftF w R θ = ((liftRho w R θ : ℝ) : ℂ) *
      Complex.exp (((liftAngle w R θ : ℝ) : ℂ) * Complex.I) := by
    have h : liftF w R θ = (liftF w R θ * Complex.exp (-(Complex.I * ((liftAngle w R θ : ℝ) : ℂ)))) *
        Complex.exp (((liftAngle w R θ : ℝ) : ℂ) * Complex.I) := by
      rw [mul_assoc, hinv, mul_one]
    rw [hG1] at h
    exact h
  rw [← liftRho_eq_norm w R θ, hFeq, mul_div_cancel_left₀ _ hρne]

/-- Selftest: the hypotheses are satisfiable (w = 0, R = 1), so the conclusion is not vacuous. -/
example : ∃ α : ℝ → ℝ, ∀ θ : ℝ, HasDerivAt α (liftRate 0 1 θ) θ := by
  obtain ⟨α, h, -, -⟩ := lift_circle 0 1 one_pos (by simp)
  exact ⟨α, h⟩

end

end G2032Lift
end NlsGge.GKDefinitionDesign

