import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! SOURCE ONLY: a globally C² actual circle-to-square sector deformation.
No homotopy integral identity is assumed. Denominator positivity is earned.
Exact eight targets+English were recorded before these proofs. UNCOMPILED. -/
set_option autoImplicit false
open Set
namespace NlsGge.GK38
noncomputable section

def p6SquareSectorScale38 (t y : ℝ) : ℝ :=
  (1-t)/Real.sqrt (1+y^2)+t

def p6SquareSector38 (c : ℂ) (r t y : ℝ) : ℂ :=
  c+(r*p6SquareSectorScale38 t y) • ((1 : ℂ)+(y : ℂ)*Complex.I)

theorem p6SquareSectorScale_bounds38 (t y : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ p6SquareSectorScale38 t y ∧ p6SquareSectorScale38 t y ≤ 1 ∧
    p6SquareSectorScale38 t y*Real.sqrt (1+y^2) = (1-t)+t*Real.sqrt (1+y^2) := by
  have hpos : 0 < Real.sqrt (1+y^2) := Real.sqrt_pos.mpr (by positivity)
  have hone : 1 ≤ Real.sqrt (1+y^2) := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg y])
  have hleft : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  have hdiv : (1-t)/Real.sqrt (1+y^2) ≤ 1-t := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_nonneg hleft (sub_nonneg.mpr hone)]
  refine ⟨add_nonneg (div_nonneg hleft hpos.le) ht.1, ?_, ?_⟩
  · unfold p6SquareSectorScale38
    linarith
  · unfold p6SquareSectorScale38
    field_simp

theorem p6SquareSector_geometry38 (c : ℂ) (r t y : ℝ) (hr : 0 ≤ r)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hy : |y| ≤ 1) :
    r ≤ ‖p6SquareSector38 c r t y-c‖ ∧
    |(p6SquareSector38 c r t y).re-c.re| ≤ r ∧
    |(p6SquareSector38 c r t y).im-c.im| ≤ r := by
  have hs := p6SquareSectorScale_bounds38 t y ht
  have hlam : 0 ≤ r*p6SquareSectorScale38 t y := mul_nonneg hr hs.1
  have hlamr : r*p6SquareSectorScale38 t y ≤ r := by
    simpa using mul_le_mul_of_nonneg_left hs.2.1 hr
  have hunit : ‖(1 : ℂ)+(y : ℂ)*Complex.I‖ = Real.sqrt (1+y^2) := by
    simp [Complex.norm_def, Complex.normSq_apply, pow_two]
  have hnorm : ‖p6SquareSector38 c r t y-c‖ =
      r*((1-t)+t*Real.sqrt (1+y^2)) := by
    simp only [p6SquareSector38, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hlam, hunit]
    rw [mul_assoc, hs.2.2]
  have hre : (p6SquareSector38 c r t y-c).re = r*p6SquareSectorScale38 t y := by
    simp [p6SquareSector38]
  have him : (p6SquareSector38 c r t y-c).im = r*p6SquareSectorScale38 t y*y := by
    simp [p6SquareSector38, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hnorm]
    have hone : 1 ≤ Real.sqrt (1+y^2) := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg y])
    nlinarith [mul_nonneg hr (mul_nonneg ht.1 (sub_nonneg.mpr hone))]
  · have he : |(p6SquareSector38 c r t y-c).re| ≤ r := by
      rw [hre, abs_of_nonneg hlam]
      exact hlamr
    simpa only [Complex.sub_re] using he
  · have he : |(p6SquareSector38 c r t y-c).im| ≤ r := by
      rw [him, abs_mul, abs_of_nonneg hlam]
      exact (mul_le_mul_of_nonneg_left hy hlam).trans (by simpa using hlamr)
    simpa only [Complex.sub_im] using he

theorem p6SquareSector_contDiff38 (c : ℂ) (r : ℝ) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => p6SquareSector38 c r p.1 p.2) := by
  have hbase : ContDiff ℝ 2 (fun p : ℝ × ℝ => 1+p.2^2) := by fun_prop
  have hden : ContDiff ℝ 2 (fun p : ℝ × ℝ => Real.sqrt (1+p.2^2)) :=
    hbase.sqrt (fun p => by positivity)
  have hscale : ContDiff ℝ 2 (fun p : ℝ × ℝ => p6SquareSectorScale38 p.1 p.2) := by
    exact ((contDiff_const.sub contDiff_fst).div hden (fun p => by positivity)).add contDiff_fst
  have hreal : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  have hline : ContDiff ℝ 2 (fun p : ℝ × ℝ => (1 : ℂ)+(p.2 : ℂ)*Complex.I) :=
    contDiff_const.add (hreal.mul contDiff_const)
  exact contDiff_const.add ((contDiff_const.mul hscale).smul hline)

theorem p6SquareSector_at_zero38 (c : ℂ) (r y : ℝ) :
    p6SquareSector38 c r 0 y = circleMap c r (Real.arctan y) := by
  have hcircle : circleMap c r (Real.arctan y) = c+circleMap 0 r (Real.arctan y) := by
    simp [circleMap]
  rw [hcircle]
  unfold p6SquareSector38
  apply congrArg (fun w : ℂ => c+w)
  have hden : Real.sqrt (1+y^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  apply Complex.ext
  · simp [p6SquareSectorScale38, circleMap_zero_re, Real.cos_arctan, div_eq_mul_inv]
    field_simp [hden]
    simp
  · simp [p6SquareSectorScale38, circleMap_zero_im, Real.sin_arctan, div_eq_mul_inv]
    field_simp [hden]

theorem p6SquareSector_at_one38 (c : ℂ) (r y : ℝ) :
    p6SquareSector38 c r 1 y = c+r • ((1 : ℂ)+(y : ℂ)*Complex.I) := by
  simp [p6SquareSector38, p6SquareSectorScale38]

theorem p6SquareSector_endpoint_rotation38 (c : ℂ) (r t : ℝ) :
    p6SquareSector38 c r t 1 = c+Complex.I*(p6SquareSector38 c r t (-1)-c) := by
  apply Complex.ext
  <;> simp [p6SquareSector38, p6SquareSectorScale38]

end
end NlsGge.GK38
