import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot.ImaginaryResolventKernelAPIProbeV2

open MeasureTheory

/-- The positive scalar kernel used for the full signed imaginary resolvent. -/
def scalarKernel (y x : ℝ) : ℝ := (y ^ 2 + (Real.pi * x) ^ 2)⁻¹

theorem scalarKernel_pos {y x : ℝ} (hy : 0 < y) : 0 < scalarKernel y x := by
  unfold scalarKernel
  positivity

theorem scalarKernel_nonneg {y x : ℝ} (hy : 0 < y) : 0 ≤ scalarKernel y x :=
  le_of_lt (scalarKernel_pos hy)

theorem scalarKernel_even (y : ℝ) (x : ℝ) : scalarKernel y (-x) = scalarKernel y x := by
  simp [scalarKernel, mul_neg, neg_sq]

theorem scalarKernel_antitoneOn_Ici {y : ℝ} (hy : 0 < y) :
    AntitoneOn (scalarKernel y) (Set.Ici 0) := by
  intro x hx z hz hxz
  unfold scalarKernel
  have hden : y ^ 2 + (Real.pi * x) ^ 2 ≤ y ^ 2 + (Real.pi * z) ^ 2 := by
    have hpx : 0 ≤ Real.pi * x := mul_nonneg (le_of_lt Real.pi_pos) hx
    have hpz : 0 ≤ Real.pi * z := mul_nonneg (le_of_lt Real.pi_pos) hz
    have hmul : Real.pi * x ≤ Real.pi * z :=
      mul_le_mul_of_nonneg_left hxz (le_of_lt Real.pi_pos)
    have hsquare : (Real.pi * x) ^ 2 ≤ (Real.pi * z) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hmul) (add_nonneg hpx hpz)]
    nlinarith
  have hone : 0 < y ^ 2 + (Real.pi * x) ^ 2 := by positivity
  simpa only [one_div] using one_div_le_one_div_of_le hone hden

/-- Exact half-line integral. The scaling is `u = π*x/y`, and the primitive
is the pinned `arctan` integral of `(1+u²)⁻¹`. -/
theorem scalarKernel_integral_Ioi_zero {y : ℝ} (hy : 0 < y) :
    ∫ x in Set.Ioi (0 : ℝ), scalarKernel y x = 1 / (2 * y) := by
  let b : ℝ := Real.pi / y
  have hb : 0 < b := by dsimp [b]; positivity
  have hpoint (x : ℝ) : scalarKernel y x =
      (y ^ 2)⁻¹ * (1 + (b * x) ^ 2)⁻¹ := by
    dsimp [scalarKernel, b]
    have hden : 1 + (Real.pi / y * x) ^ 2 ≠ 0 := by positivity
    field_simp [ne_of_gt hy, hden]
    <;> ring
  calc
    ∫ x in Set.Ioi (0 : ℝ), scalarKernel y x
        = (y ^ 2)⁻¹ * ∫ x in Set.Ioi (0 : ℝ), (1 + (b * x) ^ 2)⁻¹ := by
          simp_rw [hpoint, integral_const_mul]
    _ = (y ^ 2)⁻¹ * (b⁻¹ * (Real.pi / 2)) := by
          rw [integral_comp_mul_left_Ioi (fun u : ℝ => (1 + u ^ 2)⁻¹) 0 hb]
          simp
    _ = 1 / (2 * y) := by
          dsimp [b]
          field_simp [ne_of_gt hy]
          <;> ring

end NlsGge.Pilot.ImaginaryResolventKernelAPIProbeV2
