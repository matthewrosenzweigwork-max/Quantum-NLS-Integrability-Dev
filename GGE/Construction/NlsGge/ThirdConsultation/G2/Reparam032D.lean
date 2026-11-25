import Mathlib

                                                                                                         
                                                                                             
                                                           
                                                                                              
                                                                                                  
                                                                                             
set_option autoImplicit false

namespace NlsGge.GKDefinitionDesign
namespace G2032Homotopy
noncomputable section

/-- Projection of `w` on the ray direction `e^{iα}`. -/
def rayB (w : ℂ) (α : ℝ) : ℝ := w.re * Real.cos α + w.im * Real.sin α

/-- Discriminant of the ray quadratic, with `‖w‖² = w.re² + w.im²`. -/
def rayD (w : ℂ) (R : ℝ) (α : ℝ) : ℝ := rayB w α ^ 2 - (w.re ^ 2 + w.im ^ 2) + R ^ 2

/-- Exit radius of the disc of radius `R` about `τ − w`, along the ray from `τ` at angle `α`. -/
def rayR (w : ℂ) (R : ℝ) (α : ℝ) : ℝ := -rayB w α + Real.sqrt (rayD w R α)

theorem re_point (w : ℂ) (α r : ℝ) :
    (w + (r : ℂ) * Complex.exp ((α : ℂ) * Complex.I)).re = w.re + r * Real.cos α := by
  simp [Complex.exp_ofReal_mul_I_re]

theorem im_point (w : ℂ) (α r : ℝ) :
    (w + (r : ℂ) * Complex.exp ((α : ℂ) * Complex.I)).im = w.im + r * Real.sin α := by
  simp [Complex.exp_ofReal_mul_I_im]

/-- The squared distance from `-w` (i.e. from `C`) to the point `τ + r e^{iα}`. -/
theorem normSq_point (w : ℂ) (α r : ℝ) :
    Complex.normSq (w + (r : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) =
      (w.re ^ 2 + w.im ^ 2) + 2 * r * rayB w α + r ^ 2 := by
  rw [Complex.normSq_apply, re_point, im_point]
  unfold rayB
  linear_combination (r ^ 2) * Real.cos_sq_add_sin_sq α

theorem rayD_gt (w : ℂ) (R : ℝ) (α : ℝ) (hwR : w.re ^ 2 + w.im ^ 2 < R ^ 2) :
    rayB w α ^ 2 < rayD w R α := by
  unfold rayD
  linarith

theorem abs_rayB_lt_sqrt (w : ℂ) (R : ℝ) (α : ℝ) (hwR : w.re ^ 2 + w.im ^ 2 < R ^ 2) :
    |rayB w α| < Real.sqrt (rayD w R α) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (rayD_gt w R α hwR)

theorem rayR_pos (w : ℂ) (R : ℝ) (α : ℝ) (hwR : w.re ^ 2 + w.im ^ 2 < R ^ 2) :
    0 < rayR w R α := by
  have h1 := abs_rayB_lt_sqrt w R α hwR
  have h2 := le_abs_self (rayB w α)
  unfold rayR
  linarith

theorem rayD_nonneg (w : ℂ) (R : ℝ) (α : ℝ) (hwR : w.re ^ 2 + w.im ^ 2 < R ^ 2) :
    0 ≤ rayD w R α :=
  le_of_lt (lt_of_le_of_lt (sq_nonneg _) (rayD_gt w R α hwR))

/-- On the exit radius the point lies exactly on the circle of radius `R`. -/
theorem normSq_rayR (w : ℂ) (R : ℝ) (α : ℝ) (hwR : w.re ^ 2 + w.im ^ 2 < R ^ 2) :
    Complex.normSq (w + (rayR w R α : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) = R ^ 2 := by
  rw [normSq_point]
  have hs : Real.sqrt (rayD w R α) ^ 2 = rayD w R α := Real.sq_sqrt (rayD_nonneg w R α hwR)
  unfold rayR
  unfold rayD at hs ⊢
  linear_combination hs

/-- Every point of the ray segment up to the exit radius lies in the closed disc. -/
theorem normSq_le_of_le_rayR (w : ℂ) (R : ℝ) (α r : ℝ) (hwR : w.re ^ 2 + w.im ^ 2 < R ^ 2)
    (hr0 : 0 ≤ r) (hr : r ≤ rayR w R α) :
    Complex.normSq (w + (r : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) ≤ R ^ 2 := by
  rw [normSq_point]
  have hs : Real.sqrt (rayD w R α) ^ 2 = rayD w R α := Real.sq_sqrt (rayD_nonneg w R α hwR)
  have hsn : 0 ≤ Real.sqrt (rayD w R α) := Real.sqrt_nonneg _
  have hb := abs_rayB_lt_sqrt w R α hwR
  have hlow : -Real.sqrt (rayD w R α) < rayB w α := by
    have := (abs_lt.mp hb).1
    linarith
  have hup : r + rayB w α ≤ Real.sqrt (rayD w R α) := by
    unfold rayR at hr
    linarith
  have h1 : 0 ≤ Real.sqrt (rayD w R α) - (r + rayB w α) := by linarith
  have h2 : 0 ≤ Real.sqrt (rayD w R α) + (r + rayB w α) := by linarith
  have hm := mul_nonneg h1 h2
  unfold rayD at hs hm
  nlinarith [hm, hs]

/-- Strict form: a point strictly inside the disc lies strictly before the exit radius. -/
theorem lt_rayR_of_normSq_lt (w : ℂ) (R : ℝ) (α r : ℝ) (hwR : w.re ^ 2 + w.im ^ 2 < R ^ 2)
    (hr0 : 0 ≤ r)
    (h : Complex.normSq (w + (r : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) < R ^ 2) :
    r < rayR w R α := by
  rw [normSq_point] at h
  have hs : Real.sqrt (rayD w R α) ^ 2 = rayD w R α := Real.sq_sqrt (rayD_nonneg w R α hwR)
  have hsn : 0 ≤ Real.sqrt (rayD w R α) := Real.sqrt_nonneg _
  by_contra hc
  have hc' : rayR w R α ≤ r := not_lt.mp hc
  have hge : Real.sqrt (rayD w R α) ≤ r + rayB w α := by
    unfold rayR at hc'
    linarith
  have h2 : 0 ≤ (r + rayB w α) + Real.sqrt (rayD w R α) := by linarith
  have hm := mul_nonneg (sub_nonneg.mpr hge) h2
  unfold rayD at hs hm
  nlinarith [hm, hs, h]

/-- Selftest: the hypotheses are satisfiable and the radius is the expected value. -/
example : rayR 0 1 0 = 1 := by
  simp [rayR, rayD, rayB]

example : Complex.normSq ((0 : ℂ) + ((rayR 0 1 0 : ℝ) : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) = 1 := by
  have h := normSq_rayR 0 1 0 (by norm_num)
  simpa using h

end
end G2032Homotopy
end NlsGge.GKDefinitionDesign

