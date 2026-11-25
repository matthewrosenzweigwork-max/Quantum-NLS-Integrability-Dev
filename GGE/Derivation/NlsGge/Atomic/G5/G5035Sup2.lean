import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5018M5a
import NlsGge.Atomic.G3.G3031All

/- G5-035 SUPPORT 2 `G5035Sup2` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5035Sup2.lean, namespace NlsGge.GKDefinitionDesign.G5035Sup2.
   `angle_local_primitive`: at a real point with open j-gap the angle differential has a local complex-analytic primitive.
   The construction is byte-identical in substance to the `hprim` block of the landed G5031 proof (landed G5018M5a lift
   `g5018_diagonal_local_lift` plus `betaSum_analyticOnNhd_sourceBetaW`); it is exported once here so that G5-035 and G5-036 do not
   repeat it.  No sourceFamily.XY_analytic. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G5035Sup2
noncomputable section

theorem angle_local_primitive (w : PhysicalL2) (j : ℤ) (hj : gamma2 (realSlice w) j ≠ 0) :
    ∃ (V : Set PotPair) (θ : PotPair → ℂ), IsOpen V ∧ realSlice w ∈ V ∧
      AnalyticOnNhd ℂ θ V ∧ ∀ ψ ∈ V, fderiv ℂ θ ψ = angleDerivative j ψ := by
  obtain ⟨V, e, hV, hw, hVsub, he, -, hder⟩ := g5018_diagonal_local_lift w j hj
  have hβ : AnalyticOnNhd ℂ (betaSum j) V :=
    (betaSum_analyticOnNhd_sourceBetaW j).mono (fun ψ hψ => (hVsub hψ).1)
  refine ⟨V, fun ψ => e ψ + betaSum j ψ, hV, hw, he.add hβ, ?_⟩
  intro ψ hψ
  have h1 : HasFDerivAt (fun ψ => e ψ + betaSum j ψ)
      (fderiv ℂ e ψ + fderiv ℂ (betaSum j) ψ) ψ :=
    ((he ψ hψ).differentiableAt.hasFDerivAt).add ((hβ ψ hψ).differentiableAt.hasFDerivAt)
  rw [h1.fderiv, ← hder ψ hψ]
  abel

end
end G5035Sup2
end NlsGge.GKDefinitionDesign
