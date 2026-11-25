import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.G5.G5017Host
import NlsGge.ThirdConsultation.G5.G5017Support1

                                                                                                                      
                                                    
                                                                                                                       
                                                                                                         
                                                                                                                         
                                                                                                                    
                                                             
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.G5017Support1

namespace NlsGge.ThirdConsultation.KSN
namespace KSN001Aux
noncomputable section

/-- (M3) of KSN001_STOP.md: analyticity of the complex bracket. -/
theorem pairPoisson_analyticOnNhd (f g : PotPair → ℂ) (hf : AnalyticOnNhd ℂ f sourceBetaW)
    (hg : AnalyticOnNhd ℂ g sourceBetaW) :
  AnalyticOnNhd ℂ (pairPoisson f g) sourceBetaW := by
  intro φ hφ
  let K : (PotPair →L[ℂ] ℂ) →L[ℂ] PotPair :=
    ((-Complex.I) • (ContinuousLinearMap.snd ℂ PhysicalL2 PhysicalL2).comp pairGradientL).prod
      (Complex.I • (ContinuousLinearMap.fst ℂ PhysicalL2 PhysicalL2).comp pairGradientL)
  let B : (PotPair →L[ℂ] ℂ) →L[ℂ] PotPair →L[ℂ] ℂ := ContinuousLinearMap.id ℂ (PotPair →L[ℂ] ℂ)
  have hP : pairPoisson f g = fun ψ => B (fderiv ℂ f ψ) (K (fderiv ℂ g ψ)) := by
    funext ψ
    rfl
  rw [hP]
  have h1 : AnalyticAt ℂ (fderiv ℂ f) φ := hf.fderiv φ hφ
  have h2 : AnalyticAt ℂ (fun ψ => K (fderiv ℂ g ψ)) φ := (K.analyticAt _).comp (hg.fderiv φ hφ)
  exact (B.analyticAt_bilinear (fderiv ℂ f φ, K (fderiv ℂ g φ))).comp₂ h1 h2

end
end KSN001Aux
end NlsGge.ThirdConsultation.KSN
