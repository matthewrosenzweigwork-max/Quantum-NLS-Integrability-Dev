import NlsGge.GK38.StdRootBranchesProducts

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G2_023 :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => canonRoot38 p.1 p.2) rootDomain38 ∧
    (∀ p ∈ rootDomain38,
      canonRoot38 p.1 p.2 ≠ 0 ∧
      (canonRoot38 p.1 p.2)^2 = (discrim p.1 p.2)^2-4) ∧
    (∀ z : ℂ, z ∉ gapSegments38 0 →
      canonRoot38 0 z = -2*Complex.I*Complex.sin z) := by
  refine ⟨canonRoot_analytic38, ?_, ?_⟩
  · intro p hp
    obtain ⟨hφ, hz⟩ := hp
    refine ⟨canonRoot_ne_zero38 p.1 hφ p.2 hz, ?_⟩
    exact (canonRoot_sq38 p.1 hφ p.2 hz).trans rfl
  · intro z hz
    exact canonRoot_free38 z hz


end
end NlsGge.GKDefinitionDesign
