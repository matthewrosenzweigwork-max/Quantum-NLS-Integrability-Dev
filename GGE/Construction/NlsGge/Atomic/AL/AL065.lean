import Mathlib
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALPositiveDecompositions38
                                                                                                                                                                                                                                                                
                                         

                                                                                            
                                                                                                       
                                                     
                                                                                                
                                                                                           
                                                                                                  
                                                                                                
                                         

set_option autoImplicit false

open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.AL

noncomputable def logRemainder2 (r : ℝ) : ℝ := alEll r - r ^ 2 / 2

theorem al065 (M : ℝ) (hM : 0 ≤ M) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ h : ℝ, 0 < h → h < δ → ∀ v : ℂ, ‖v‖ ≤ M →
        h ^ 2 * ‖v‖ ^ 2 ≤ 1 / 2 ∧
        |alEll (h ^ 2 * ‖v‖ ^ 2) - h ^ 4 * ‖v‖ ^ 4 / 2| ≤ C * h ^ 6 ∧
        |logRemainder2 (h ^ 2 * ‖v‖ ^ 2) - h ^ 6 * ‖v‖ ^ 6 / 3| ≤ C * h ^ 8 := by
  refine ⟨1 / (2 * (M + 1)), div_pos one_pos (by linarith), 2 * (M ^ 6 + M ^ 8), by positivity, ?_⟩
  intro h hh0 hhδ v hv
  have hδ : h * (2 * (M + 1)) < 1 := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * (M + 1))).1 hhδ
    linarith
  have hx : h * M < 1 / 2 := by nlinarith
  have hnv : 0 ≤ ‖v‖ := norm_nonneg v
  have hxv : h * ‖v‖ ≤ h * M := mul_le_mul_of_nonneg_left hv hh0.le
  have hxv0 : 0 ≤ h * ‖v‖ := mul_nonneg hh0.le hnv
  have hxlt : h * ‖v‖ < 1 / 2 := lt_of_le_of_lt hxv hx
  have hr_half : h ^ 2 * ‖v‖ ^ 2 ≤ 1 / 2 := by nlinarith [mul_nonneg hxv0 hxv0]
  have hr0 : 0 ≤ h ^ 2 * ‖v‖ ^ 2 := by positivity
  refine ⟨hr_half, ?_, ?_⟩
  · -- clause 2: |alEll r - r^2/2| <= 2 r^3 with r = h^2 ||v||^2
    have e1 : h ^ 4 * ‖v‖ ^ 4 / 2 = (h ^ 2 * ‖v‖ ^ 2) ^ 2 / 2 := by ring
    rw [e1]
    have hq := alEll_quad_38 hr0 hr_half
    have e3 : (h ^ 2 * ‖v‖ ^ 2) ^ 3 = h ^ 6 * ‖v‖ ^ 6 := by ring
    rw [e3] at hq
    have hM6 : ‖v‖ ^ 6 ≤ M ^ 6 := pow_le_pow_left₀ hnv hv 6
    have hh6 : 0 ≤ h ^ 6 := by positivity
    have k1 : h ^ 6 * ‖v‖ ^ 6 ≤ h ^ 6 * M ^ 6 := mul_le_mul_of_nonneg_left hM6 hh6
    have k2 : 0 ≤ M ^ 8 * h ^ 6 := by positivity
    calc _ ≤ 2 * (h ^ 6 * ‖v‖ ^ 6) := hq
      _ ≤ 2 * (M ^ 6 + M ^ 8) * h ^ 6 := by nlinarith
  · -- clause 3: |logRemainder2 r - r^3/3| <= 2 r^4 with r = h^2 ||v||^2
    have e4 : logRemainder2 (h ^ 2 * ‖v‖ ^ 2) - h ^ 6 * ‖v‖ ^ 6 / 3
        = -Real.log (1 - h ^ 2 * ‖v‖ ^ 2) - h ^ 2 * ‖v‖ ^ 2 - (h ^ 2 * ‖v‖ ^ 2) ^ 2 / 2
            - (h ^ 2 * ‖v‖ ^ 2) ^ 3 / 3 := by
      unfold logRemainder2 alEll; ring
    rw [e4]
    have hl := alLog4_38 hr0 hr_half
    have hM8 : ‖v‖ ^ 8 ≤ M ^ 8 := pow_le_pow_left₀ hnv hv 8
    have hh8 : 0 ≤ h ^ 8 := by positivity
    have k1 : h ^ 8 * ‖v‖ ^ 8 ≤ h ^ 8 * M ^ 8 := mul_le_mul_of_nonneg_left hM8 hh8
    have k2 : 0 ≤ M ^ 6 * h ^ 8 := by positivity
    calc _ ≤ 2 * (h ^ 2 * ‖v‖ ^ 2) ^ 4 := hl
      _ = 2 * (h ^ 8 * ‖v‖ ^ 8) := by ring
      _ ≤ 2 * (M ^ 6 + M ^ 8) * h ^ 8 := by nlinarith

end NlsGge.ThirdConsultation.AL

