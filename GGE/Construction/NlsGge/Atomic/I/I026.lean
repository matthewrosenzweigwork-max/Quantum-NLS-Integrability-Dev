import Mathlib
import NlsGge.Atomic.I.I026Core
import NlsGge.ThirdConsultation.I.ActualInverseBridge

                                                                                                                                                                                                                                           
                                                                          
                                                                                                      
                                                                                                             
                         
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i026 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    let W := weight c.val
    Tendsto (fun N : ℕ => finiteRelativeNormalizer W (Λ N)) atTop
      (𝓝 (limitNormalizer W)) ∧
    (∀ N : ℕ, finiteRelativeNormalizer W (Λ N) =
      ∫ z : ℤ → ℂ, Real.exp (-remainderForWeight W
        (physicalOfSequence (projFin38 (Λ N) z))) ∂fullWeightSequenceGaussian c.val) ∧
    ∀ m : ℕ, IsProbabilityMeasure ((physicalLaw W).map (physFS38 m)) ∧
      (∀ N : ℕ, IsProbabilityMeasure ((finiteGapLaw W (Λ N)).map (physFS38 m))) ∧
      ∀ F : SobolevHilbert (m : ℝ) →ᵇ ℝ,
        Tendsto (fun N : ℕ => ∫ u : PhysicalL2, F (physFS38 m u) ∂finiteGapLaw W (Λ N))
          atTop (𝓝 (∫ u : PhysicalL2, F (physFS38 m u) ∂physicalLaw W)) :=
  NlsGge.ThirdConsultation.I026C.i026_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lower upper c Λ hΛ

end NlsGge.ThirdConsultation.I
