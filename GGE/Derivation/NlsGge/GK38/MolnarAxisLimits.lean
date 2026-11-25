import NlsGge.GK38.MolnarAxisKernels

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace NlsGge.GK38.MolnarBounds38

open NlsGge.Pilot NlsGge.Schur NlsGge.SpectralFoundations

/-- Exact imaginary-axis identities; all Cauchy kernels are integrable before projection. -/
theorem actual_shift_axis_formulas38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (y : ℝ) (hy : 1 ≤ y) :
    y * (molnarShift38 u (Complex.I * (y : ℂ))).im =
      (1 / Real.pi) * ∫ t : ℝ, actualGapHeightE02_38 u t * (y ^ 2 / (t ^ 2 + y ^ 2)) ∧
    y * (molnarShift38 u (Complex.I * (y : ℂ))).re =
      (1 / Real.pi) * ((1 / y) *
        ∫ t : ℝ, (t * actualGapHeightE02_38 u t) * (y ^ 2 / (t ^ 2 + y ^ 2))) := by
  obtain ⟨hi, heq⟩ := actual_shift_herglotz38 u hu (Complex.I * (y : ℂ)) (by simp; linarith)
  have hcoef : (1 / Real.pi : ℂ) = ((1 / Real.pi : ℝ) : ℂ) := by push_cast; rfl
  have him : (molnarShift38 u (Complex.I * (y : ℂ))).im =
      (1 / Real.pi) * ∫ t : ℝ, actualGapHeightE02_38 u t * (y / (t ^ 2 + y ^ 2)) := by
    rw [heq, hcoef, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [signed_cauchy_axis_im38 _ y hy hi]
  have hre : (molnarShift38 u (Complex.I * (y : ℂ))).re =
      (1 / Real.pi) * ∫ t : ℝ, actualGapHeightE02_38 u t * (t / (t ^ 2 + y ^ 2)) := by
    rw [heq, hcoef, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [signed_cauchy_axis_re38 _ y hy hi]
  constructor
  · rw [him, hm38_Sv]
    ring
  · have hy0 : y ≠ 0 := by linarith
    rw [hre, hm38_Sw]
    field_simp [hy0, Real.pi_ne_zero]

/-- The actual imaginary-axis first coefficient equals half the physical mass. -/
theorem actual_shift_axis_mass_limit38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Tendsto (fun y : ℝ => y * (molnarShift38 u (Complex.I * (y : ℂ))).im)
      atTop (𝓝 (‖u‖ ^ 2 / 2)) ∧
    Tendsto (fun y : ℝ => y * (molnarShift38 u (Complex.I * (y : ℂ))).re)
      atTop (𝓝 0) := by
  have hmass := actualGapHeight_integral_eq_normSq_E02_38 u hu
  have hfirst := actual_height_first_moment_integrable38 u hu
  constructor
  · have h := (hm38_dct (actualGapHeightE02_38 u) hmass.1).const_mul (1 / Real.pi)
    have hm : (1 / Real.pi) * (∫ t : ℝ, actualGapHeightE02_38 u t) = ‖u‖ ^ 2 / 2 := by
      calc
        _ = ((2 / Real.pi) * (∫ t : ℝ, actualGapHeightE02_38 u t)) / 2 := by ring
        _ = _ := by rw [hmass.2]
    rw [hm] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    exact (actual_shift_axis_formulas38 u hu y hy).1.symm
  · have hinv : Tendsto (fun y : ℝ => (1 : ℝ) / y) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h := (hinv.mul (hm38_dct (fun t : ℝ => t * actualGapHeightE02_38 u t) hfirst)).const_mul
      (1 / Real.pi)
    simp only [zero_mul, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    exact (actual_shift_axis_formulas38 u hu y hy).2.symm

/-- Squaring the actual mass coefficient, with its sign fixed by the imaginary axis. -/
theorem actual_shift_square_axis_limit38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Tendsto (fun y : ℝ => y ^ 2 * (molnarShift38 u (Complex.I * (y : ℂ)) ^ 2).re)
      atTop (𝓝 (-((‖u‖ ^ 2 / 2) ^ 2))) := by
  obtain ⟨him, hre⟩ := actual_shift_axis_mass_limit38 u hu
  have h := (hre.pow 2).sub (him.pow 2)
  convert h using 1
  · funext y
    simp only [pow_two, Complex.mul_re]
    ring
  · ring

end NlsGge.GK38.MolnarBounds38
