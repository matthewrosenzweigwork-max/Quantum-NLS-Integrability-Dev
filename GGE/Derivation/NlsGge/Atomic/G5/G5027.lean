import Mathlib
import NlsGge.Atomic.G5.G5027Sup5
import NlsGge.Atomic.G3.G3031All

/- G5-027 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5027.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G5027` VERBATIM from followup12 STATEMENTS/G5.md section G5-027 (retained by Pro round 14 cluster 5; no lexical repair).
   Proof: G5027Aux.g5027_core (G5027Sup5, worker-lane compiled) applied to the landed betaSum_analyticOnNhd_sourceBetaW (G3031All);
   its inline closure exceeds worker-lane memory, so this file needs a main-lane check by root.  hiso is not needed by the proof. -/
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
