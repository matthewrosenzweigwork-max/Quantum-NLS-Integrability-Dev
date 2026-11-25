import Mathlib
import NlsGge.Atomic.G5.G5027Sup5
import NlsGge.Atomic.G3.G3031All

                                                                        
                                                                           
                                                                                                                                 
                                                                                                                                   
                                                                                                                                    
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5027 (k m : ℤ) (u₀ : PhysicalL2) (u : ℕ → PhysicalL2)
    (hgap : gamma2 (realSlice u₀) k ≠ 0)
    (hleft : gkMu u₀ k = actualGapLowerAllE02_38 u₀ k)
    (hiso : ∀ j : ℕ, u j ∈ isospectralSet u₀)
    (hinterior : ∀ j : ℕ, InteriorRealDirichletGap k (u j))
    (hlim : Tendsto u atTop (𝓝 u₀)) :
  (∀ j : ℕ, antiDiscrim (realSlice (u j)) (muSeq (realSlice (u j)) k) ≠ 0) ∧
  Tendsto (fun j : ℕ =>
    let φ := realSlice (u j)
    pairGradientCLM (angleIntegralDerivative k m φ) -
      (psiAt m (muSeq φ k) φ / antiDiscrim φ (muSeq φ k)) •
        (pairGradient (fun ψ => muSeq ψ k) φ -
          pairGradient (fun ψ => lamMinus ψ k) φ)) atTop (𝓝 0) :=
  G5027Aux.g5027_core k m u₀ u hgap hleft hinterior hlim (betaSum_analyticOnNhd_sourceBetaW k)

end
end NlsGge.GKDefinitionDesign
