import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationC2

/-! # Explicit Borel frequencies on each finite plane

The section has real nonnegative coordinates sqrt(a_i). On positive actions
the angular frequency is minus the imaginary vector-field component divided
by sqrt(a_i); it is explicitly zero on nonpositive actions. Radial equivariance
and tangency prove the vector identity, with a separate zero-coordinate case.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Birkhoff

/-- The explicit nonnegative real square-root section of finite-plane actions.
It is defined on the whole real product carrier, using the usual real sqrt. -/
def finitePlaneSection38 (Λ : Finset ℤ) (a : ℤ → ℝ) (i : Λ) : ℂ :=
  (Real.sqrt (a i.1) : ℂ)

/-- The angular frequency read from the square-root section at one coordinate.
The quotient is used only at strictly positive action; elsewhere it is zero. -/
def finitePlaneFrequency38 (Λ : Finset ℤ) (i : Λ) (a : ℤ → ℝ) : ℝ :=
  if 0 < a i.1 then -(YΛ Λ (finitePlaneSection38 Λ a) i).im / Real.sqrt (a i.1) else 0

/-- Each coordinate of the finite Hamiltonian vector field is continuous,
by real analyticity of the literal Hamiltonian and continuity of its derivative. -/
theorem continuous_YLambda38 (Λ : Finset ℤ) (i : Λ) :
    Continuous (fun w : Λ → ℂ => YΛ Λ w i) := by
  have hH : ContDiff ℝ 1 (HΛ Λ) := (analytic_HLambda38 Λ).contDiff
  have hc (η : Λ → ℂ) : Continuous (fun w : Λ → ℂ => fderiv ℝ (HΛ Λ) w η) :=
    (hH.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  unfold YΛ
  exact continuous_const.mul ((Complex.continuous_ofReal.comp (hc (Pi.single i 1))).add
    (continuous_const.mul (Complex.continuous_ofReal.comp (hc (Pi.single i Complex.I)))))

/-- The explicit square-root section is continuous on the whole action product. -/
theorem continuous_finitePlaneSection38 (Λ : Finset ℤ) :
    Continuous (finitePlaneSection38 Λ) :=
  continuous_pi (fun i => Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp (continuous_apply i.1)))

/-- Each finite-plane frequency is product-Borel measurable, including the
explicit branch at zero action. No measurable choice is used. -/
theorem measurable_finitePlaneFrequency38 (Λ : Finset ℤ) (i : Λ) :
    Measurable (finitePlaneFrequency38 Λ i) := by
  unfold finitePlaneFrequency38
  apply Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply i.1))
    _ measurable_const
  exact ((Complex.continuous_im.comp ((continuous_YLambda38 Λ i).comp (continuous_finitePlaneSection38 Λ))).measurable.neg).div
    (Real.continuous_sqrt.measurable.comp (measurable_pi_apply i.1))

set_option maxHeartbeats 400000 in
/-- The explicit finite-plane frequencies give the vector field at every
finite vector, including coordinates of zero action. -/
theorem finitePlaneFrequency_vector38 (Λ : Finset ℤ) (w : Λ → ℂ) (i : Λ) :
    YΛ Λ w i = -Complex.I *
      (finitePlaneFrequency38 Λ i (fun k => ‖extZero38 Λ w k‖ ^ 2) : ℂ) * w i := by
  let a : ℤ → ℝ := fun k => ‖extZero38 Λ w k‖ ^ 2
  let s : Λ → ℂ := finitePlaneSection38 Λ a
  have hs (j : Λ) : s j = (‖w j‖ : ℂ) := by
    simp only [s, finitePlaneSection38, a, extZero38_apply_of_mem _ j.2,
      Real.sqrt_sq (norm_nonneg _)]
  have hn (j : Λ) : ‖s j‖ ^ 2 = ‖w j‖ ^ 2 := by
    rw [hs]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hrad := YLambda_radial_equivariant38 Λ s w hn
  by_cases hw : w i = 0
  · have hz := (YLambda_radial_equivariant38 Λ w w (fun _ => rfl)).2.1 i hw
    rw [hz, hw, mul_zero]
  · have hr : 0 < ‖w i‖ := norm_pos_iff.mpr hw
    have hr0 : ‖w i‖ ≠ 0 := ne_of_gt hr
    have hc0 : (‖w i‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0
    have ha : a i.1 = ‖w i‖ ^ 2 := by
      simp only [a, extZero38_apply_of_mem _ i.2]
    have hp : 0 < a i.1 := by rw [ha]; positivity
    have hRe : (YΛ Λ s i).re = 0 := by
      have hh := hrad.2.2 i
      rw [hs] at hh
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left hr0
    have hY : YΛ Λ s i = -Complex.I * (finitePlaneFrequency38 Λ i a : ℂ) * (‖w i‖ : ℂ) := by
      unfold finitePlaneFrequency38
      rw [ite_eq_left hp, ha, Real.sqrt_sq (norm_nonneg _)]
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero,
          mul_zero, zero_mul, sub_zero, hRe]
      · simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero,
          mul_zero, zero_mul, sub_zero]
        field_simp
        ring
    change YΛ Λ w i = -Complex.I * (finitePlaneFrequency38 Λ i a : ℂ) * w i
    apply mul_right_cancel₀ hc0
    calc
      YΛ Λ w i * (‖w i‖ : ℂ) = YΛ Λ s i * w i := by
        simpa only [hs] using hrad.1 i
      _ = (-Complex.I * (finitePlaneFrequency38 Λ i a : ℂ) * w i) * (‖w i‖ : ℂ) := by
        rw [hY]
        ring

end LiebLiniger.FixedPeriod.EXT
