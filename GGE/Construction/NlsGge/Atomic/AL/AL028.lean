import Mathlib
import NlsGge.Hierarchy.ALFullEnergy38
import NlsGge.Hierarchy.ALMomentsBridge38
import NlsGge.Hierarchy.ALBoundaryKappa38

                                                                        
                                                                                              
                                                             
                                                                                                                 
                                                                          
                                                                                                              
                                                                                   
set_option autoImplicit false

open Set MeasureTheory
open scoped Real

namespace NlsGge.ThirdConsultation.AL
open NlsGge.AblowitzLadik

theorem al028 {L : ℕ} [NeZero L] (hodd : Odd L)
    (α : ZMod L → ℂ) (hα : IsALField38 α)
    (h : ℝ) (hh : h = (L : ℝ)⁻¹) (j : ℕ) :
  alQ38 h α j = (h⁻¹)^(2*j+1)*alK38 α j ∧
  (∀ lam : ℝ, alVh38 h α lam = h⁻¹*alKappa38 α (h*lam)) ∧
  IntervalIntegrable
    (fun lam : ℝ => (2*Real.sin (h*lam)/h)^(2*j)*alVh38 h α lam)
    volume (-Real.pi/(2*h)) (Real.pi/(2*h)) ∧
  alQ38 h α j = (2/Real.pi) *
    ∫ lam in (-Real.pi/(2*h))..(Real.pi/(2*h)),
      (2*Real.sin (h*lam)/h)^(2*j)*alVh38 h α lam := by
  refine ⟨rfl, fun lam => rfl, ?_, ?_⟩
  · have hk : Continuous (alKappa38 α) := continuous_alKappa38 hα
    have hv : Continuous fun lam : ℝ => alVh38 h α lam :=
      continuous_const.mul (hk.comp (continuous_const.mul continuous_id))
    have hs : Continuous fun lam : ℝ => (2*Real.sin (h*lam)/h)^(2*j) :=
      ((continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))).div_const h).pow _
    rw [neg_div]
    exact (hs.mul hv).intervalIntegrable _ _
  · rw [neg_div]
    exact alQ38_spectral hα hodd hh j

end NlsGge.ThirdConsultation.AL
