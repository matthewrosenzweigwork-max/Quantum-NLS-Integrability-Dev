import Mathlib
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.X.X006
import Armstrong.Work.ActualCartesianRealTraceAction

                                                                                                               
                                                                                                             
                                                                                                            
                                                                                  
                                                                                                                           
                                                                                                                     
                                                                                 
set_option autoImplicit false

open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.Atomic.X004
open NlsGge.GKDefinitionDesign

theorem samePhi_cartesian_normalization (u : PhysicalL2) (n : ℤ) :
    (cartesianX n (realSlice u)).im = 0 ∧
    (cartesianY n (realSlice u)).im = 0 ∧
    sourceFamily.Phi u n =
      (cartesianX n (realSlice u) -
        Complex.I * cartesianY n (realSlice u)) /
        (Real.sqrt 2 : ℂ) ∧
    sourceFamily.Phi u n =
      (xiN38 n (realSlice u) / 2) *
        (gk16ActualScalarZMinus38 sourceF n (realSlice u) *
          Complex.exp (-Complex.I * betaSum n (realSlice u))) ∧
    ‖sourceFamily.Phi u n‖^2 =
      ((cartesianX n (realSlice u)).re^2 +
        (cartesianY n (realSlice u)).re^2) / 2 ∧
    ‖sourceFamily.Phi u n‖^2 =
      actualGapActionAllE02_38 u n := by
  have hreal := gk16_same_family_xy_real_trace_action38 sourceFamily.W sourceFamily.W_open
    sourceFamily.W_real sourceFamily.W_gk sourceFamily.F sourceFamily.F_analytic
    sourceFamily.F_zero sourceFamily.F_period sourceFamily.F_real sourceFamily.V
    sourceFamily.V_real sourceFamily.beta sourceFamily.beta_spec n u
  have hXIm : (cartesianX n (realSlice u)).im = 0 := hreal.1
  have hYIm : (cartesianY n (realSlice u)).im = 0 := hreal.2.1
  have hrootReal : Real.sqrt 8 * Real.sqrt 2 = 4 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  have hroot : (Real.sqrt 8 : ℂ)*(Real.sqrt 2 : ℂ) = 4 := by
    exact_mod_cast hrootReal
  have hroot8 : (Real.sqrt 8 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 8)))
  have hroot2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  have halgebra (a p m : ℂ) :
      (a/(Real.sqrt 8 : ℂ)*(p+m) -
        Complex.I*(a/((Real.sqrt 8 : ℂ)*Complex.I)*(p-m)))/
          (Real.sqrt 2 : ℂ) =
        (a*2/((Real.sqrt 8 : ℂ)*(Real.sqrt 2 : ℂ)))*m := by
    field_simp [hroot8,hroot2,Complex.I_ne_zero] <;> ring
  have hconj3 : sourceFamily.Phi u n =
      (cartesianX n (realSlice u) -
        Complex.I * cartesianY n (realSlice u)) /
        (Real.sqrt 2 : ℂ) := by
    rw [sourceFamily.Phi_formula u n]
    simp only [cartesianX, cartesianY, gk16ScalarXModel38, gk16ScalarYModel38, sourceF, betaSum]
    rw [halgebra, hroot]
    ring
  have hsqrt2 : ‖(Real.sqrt 2 : ℂ)‖ ^ 2 = 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hnorm2 : ∀ x y : ℂ, x.im = 0 → y.im = 0 →
      ‖x - Complex.I * y‖ ^ 2 = x.re ^ 2 + y.re ^ 2 := by
    intro x y hx hy
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hx, hy] <;> ring
  have hZ : ‖cartesianX n (realSlice u) - Complex.I * cartesianY n (realSlice u)‖ ^ 2 =
      (cartesianX n (realSlice u)).re ^ 2 + (cartesianY n (realSlice u)).re ^ 2 :=
    hnorm2 _ _ hXIm hYIm
  have hconj5 : ‖sourceFamily.Phi u n‖^2 =
      ((cartesianX n (realSlice u)).re^2 +
        (cartesianY n (realSlice u)).re^2) / 2 := by
    rw [hconj3, norm_div, div_pow, hsqrt2, hZ]
  exact ⟨hXIm, hYIm, hconj3, sourceFamily.Phi_formula u n, hconj5, sourceFamily.Phi_action u n⟩

end NlsGge.Atomic.X004
