import Mathlib
import NlsGge.Birkhoff.S04FiniteGapInvariance38
import NlsGge.Atomic.PDE.PDE071

                                                                                          
                                                                                                                       
                                                                                                                        
                                                                                                       
                                                                                                                          
                                                                        
                                                                                                              
                                                  
                                                                                                               
                                                                                                                             
                                                                                                                            
                                                                                 
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.ThirdConsultation.PDE
namespace PDE074Aux
noncomputable section

theorem rotationInvariant_kappa (Ω : ℤ → (ℤ → ℝ) → ℝ) (Λ : Finset ℤ) (t : ℝ) :
    RotationInvariant (kappaΛ38 Ω Λ t) := by
  intro g z
  choose θ hθ using fun i => QuotientAddGroup.mk_surjective (g i)
  have e : NlsGge.NLS38.rotTorus g z = fun i => Complex.exp (θ i * Complex.I) * z i := by
    funext i
    simp only [NlsGge.NLS38.rotTorus]
    rw [← hθ i]
    exact congrArg (· * z i) (NlsGge.NLS38.toCircle_coe_real (θ i))
  rw [e, kappaΛ38_rotate]

theorem nu_invariant_of (B : BirkhoffTop38) (c : ℕ → ℝ) (Λ : Finset ℤ)
    (S : PhysicalL2 → PhysicalL2) (hS : Measurable S)
    (κ : (Λ → ℂ) → Λ → ℝ) (hκ : Measurable κ) (hinv : RotationInvariant κ)
    (ρ : (Λ → ℂ) → ℝ≥0∞) (hρ : Measurable ρ) (hρinv : ∀ z, ρ (twist κ z) = ρ z)
    (hnu : B.nuHat38 c Λ = volume.withDensity ρ)
    (hrot : ∀ w : Λ → ℂ, S (B.finiteGapField38 Λ w) = B.finiteGapField38 Λ (twist κ w)) :
    Measure.map S (B.nu38 c Λ) = B.nu38 c Λ := by
  have hT : Measurable (twist κ) := NlsGge.NLS38.measurable_twist _ hκ
  unfold BirkhoffTop38.nu38
  rw [Measure.map_map hS (B.measurable_finiteGapField38 Λ)]
  have hcomp : S ∘ B.finiteGapField38 Λ = B.finiteGapField38 Λ ∘ twist κ := funext hrot
  rw [hcomp, ← Measure.map_map (B.measurable_finiteGapField38 Λ) hT, hnu,
    twist_preserves_density hκ hinv hρ hρinv]

end
end PDE074Aux
end NlsGge.ThirdConsultation.PDE
