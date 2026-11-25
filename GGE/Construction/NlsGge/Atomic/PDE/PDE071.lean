import NlsGge.NLS38.TorusTwist38
import NlsGge.Atomic.PDE.PDE070

                                                                                                                    
                                                                                                                 
                                                                                                                        
                                                                                            
                                                                                                        
set_option autoImplicit false
open NlsGge.NLS38 MeasureTheory
open scoped ENNReal

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem twist_preserves_density {Λ : Finset ℤ} {κ : (Λ → ℂ) → Λ → ℝ} {ρ : (Λ → ℂ) → ℝ≥0∞}
    (hκ : Measurable κ) (hinv : RotationInvariant κ) (hρ : Measurable ρ)
    (hρinv : ∀ z, ρ (twist κ z) = ρ z) :
    Measure.map (twist κ) (volume.withDensity ρ) = volume.withDensity ρ := by
  have hinv' : ∀ (z : Λ → ℂ) (θ : Λ → ℝ),
      κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z := by
    intro z θ
    have h := hinv (fun i => ((θ i : ℝ) : AddCircle (2 * Real.pi))) z
    rw [← h]
    congr 1
    funext i
    simp only [NlsGge.NLS38.rotTorus]
    rw [NlsGge.NLS38.toCircle_coe_real]
  exact NlsGge.NLS38.map_withDensity_twist κ hκ hinv' ρ hρ hρinv

end
end NlsGge.ThirdConsultation.PDE
