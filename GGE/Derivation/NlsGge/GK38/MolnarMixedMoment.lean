import NlsGge.GK38.MolnarAxisLimits

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace NlsGge.GK38.MolnarBounds38

open NlsGge.Pilot NlsGge.Schur NlsGge.SpectralFoundations

/-- The actual signed mixed first moment; all components are absolutely integrable. -/
theorem actual_shift_mixed_moment38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Integrable (fun t : ℝ =>
      t * (actualQuasimomentumRealPartE02_38 u t - t) * actualGapHeightE02_38 u t) ∧
    (∫ t : ℝ,
      t * (actualQuasimomentumRealPartE02_38 u t - t) * actualGapHeightE02_38 u t) =
      -(Real.pi / 8) * (‖u‖ ^ 2) ^ 2 := by
  let a : ℝ → ℝ := fun t => actualQuasimomentumRealPartE02_38 u t - t
  let v : ℝ → ℝ := actualGapHeightE02_38 u
  let rho : ℝ → ℝ := fun t => 2 * a t * v t
  obtain ⟨C, _, hb⟩ := actual_shift_height_uniform_bound38 u hu
  have hfirst := actual_height_first_moment_integrable38 u hu
  have ha : Continuous a := (continuous_actualQuasimomentumRealPartE02_38 u).sub continuous_id
  have hv : Continuous v := continuous_actualGapHeightE02_38 u
  have hv0 : ∀ t, 0 ≤ v t := actualGapHeightE02_38_nonneg u
  have hmix : Integrable (fun t : ℝ => t * a t * v t) := by
    refine (hfirst.norm.const_mul C).mono' ((continuous_id.mul ha).mul hv).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    change ‖t * a t * v t‖ ≤ C * ‖t * v t‖
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv0 t)]
    calc
      |t| * |a t| * v t ≤ |t| * C * v t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hb t).1 (abs_nonneg t)) (hv0 t)
      _ = _ := by ring
  have hrho : Integrable (fun t : ℝ => t * rho t) := by
    refine (hmix.const_mul 2).congr (Eventually.of_forall fun t => ?_)
    dsimp [rho]
    ring
  have haxis : ∀ y : ℝ, 1 ≤ y →
      y ^ 2 * (molnarShift38 u (Complex.I * (y : ℂ)) ^ 2).re =
        (1 / Real.pi) * ∫ t : ℝ, (t * rho t) * (y ^ 2 / (t ^ 2 + y ^ 2)) := by
    intro y hy
    obtain ⟨hi, heq⟩ := actual_shift_square_herglotz38 u hu (Complex.I * (y : ℂ)) (by simp; linarith)
    have hcoef : (1 / Real.pi : ℂ) = ((1 / Real.pi : ℝ) : ℂ) := by push_cast; rfl
    have hre : (molnarShift38 u (Complex.I * (y : ℂ)) ^ 2).re =
        (1 / Real.pi) * ∫ t : ℝ, rho t * (t / (t ^ 2 + y ^ 2)) := by
      rw [heq, hcoef, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact congrArg (fun q : ℝ => (1 / Real.pi) * q) (signed_cauchy_axis_re38 rho y hy hi)
    calc
      _ = (1 / Real.pi) * (y ^ 2 * ∫ t : ℝ, rho t * (t / (t ^ 2 + y ^ 2))) := by
        rw [hre]
        ring
      _ = (1 / Real.pi) * ∫ t : ℝ, y ^ 2 * (rho t * (t / (t ^ 2 + y ^ 2))) := by
        rw [integral_const_mul]
      _ = _ := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        ring
  have hlim := (hm38_dct (fun t : ℝ => t * rho t) hrho).const_mul (1 / Real.pi)
  have hlim' : Tendsto (fun y : ℝ => y ^ 2 * (molnarShift38 u (Complex.I * (y : ℂ)) ^ 2).re)
      atTop (𝓝 ((1 / Real.pi) * ∫ t : ℝ, t * rho t)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    exact (haxis y hy).symm
  have heq := tendsto_nhds_unique hlim' (actual_shift_square_axis_limit38 u hu)
  have hrhoValue : (∫ t : ℝ, t * rho t) = 2 * ∫ t : ℝ, t * a t * v t := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp [rho]
    ring
  rw [hrhoValue] at heq
  refine ⟨hmix, ?_⟩
  change (∫ t : ℝ, t * a t * v t) = -(Real.pi / 8) * (‖u‖ ^ 2) ^ 2
  field_simp [Real.pi_ne_zero] at heq
  nlinarith [heq]

end NlsGge.GK38.MolnarBounds38
