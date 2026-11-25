import NlsGge.GK38.PoissonSpectralCommute

/- G1-069 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1069.lean, namespace
   NlsGge.GKDefinitionDesign. Head from followup5 STATEMENTS/G1.md section G1-069, with lambda renamed lam.
   Proof: the production theorem NlsGge.GK38.PoissonSpectral38.spectralDiscrimCommuteTarget, whose Prop
   SpectralDiscrimCommuteTarget is exactly the head quantified over (phi, z, w). No hypothesis is added. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.PoissonSpectral38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G1_069 (φ : PotPair) (lam μ : ℂ) :
    IntervalIntegrable (spectralGradientWedge38 φ lam μ) volume 0 1 ∧
    spectralDiscrimPoisson38 φ lam μ = 0 ∧
    gradDiscrimCLM φ lam (spectralDiscrimHamField38 φ μ) =
      spectralDiscrimPoisson38 φ lam μ :=
  NlsGge.GK38.PoissonSpectral38.spectralDiscrimCommuteTarget φ lam μ

end
end NlsGge.GKDefinitionDesign
