import Mathlib
import NlsGge.Atomic.G5.G5026
import NlsGge.Atomic.G5.G5018M5a
import NlsGge.Atomic.G3.G3031All
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5031Sup3

                                                                        
                                                                           
                                                                                                                                   
                                                                                                                                           
                                                                                                                         
                                                                                   
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5031 (u : PhysicalL2) (m n k : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) :
  CircleIntegrable (fun lam =>
    doubleAngleDiscriminantBracket m n (realSlice u) lam / canonRoot38 (realSlice u) lam)
    (discC (realSlice u) k) (discR (realSlice u) k) ∧
  abelianPeriod38 k (realSlice u) (doubleAngleDiscriminantBracket m n (realSlice u)) = 0 := by
  refine G5031Sup3.core31 u m n k hm hn (fun w j i hj => G5026 w i j hj) ?_
  intro w j hj
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
end NlsGge.GKDefinitionDesign
