                                                                                                                                              
import NlsGge.Atomic.PDE.PDE069
import NlsGge.NLS38.TorusTwist38

                                                                                    
                                                                                                                      
                                                                                                     
                                                                                                    
                                                                                                  

set_option autoImplicit false
open NlsGge.NLS38 MeasureTheory
open scoped ENNReal

namespace NlsGge.ThirdConsultation.PDE
noncomputable section


def RotationInvariant {Λ : Finset ℤ}
    (κ : (Λ → ℂ) → Λ → ℝ) : Prop :=
  ∀ g : Torus Λ, ∀ z : Λ → ℂ,
    κ (NlsGge.NLS38.rotTorus g z) = κ z

theorem twist_lintegral {Λ : Finset ℤ} {κ : (Λ → ℂ) → Λ → ℝ} {f : (Λ → ℂ) → ℝ≥0∞}
    (hκ : Measurable κ) (hinv : RotationInvariant κ) (hf : Measurable f) :
    ∫⁻ z, f (twist κ z) ∂volume = ∫⁻ z, f z ∂volume := by
  have hinv' : ∀ (z : Λ → ℂ) (θ : Λ → ℝ),
      κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z := by
    intro z θ
    have h := hinv (fun i => ((θ i : ℝ) : AddCircle (2 * Real.pi))) z
    rw [← h]
    congr 1
    funext i
    simp only [NlsGge.NLS38.rotTorus]
    rw [NlsGge.NLS38.toCircle_coe_real]
  exact NlsGge.NLS38.lintegral_comp_twist κ hκ hinv' f hf

end
end NlsGge.ThirdConsultation.PDE
