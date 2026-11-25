import NlsGge.Atomic.G1.G1067
import NlsGge.ThirdConsultation.G1.G1WronskianHost

/- G1-068 HOST01 (proof development, AUTHOR; not reviewed). Target module NlsGge/ThirdConsultation/G1/G1068Host.lean.
   Hosts the one new design name fourSolutionWronskianRhs (DEFINITIONS/G1.lean.md, followup5, lines 297-302),
   body byte-identical. solution is imported from the landed G1-067 module; wedge from G1WronskianHost. -/
set_option autoImplicit false

open NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def fourSolutionWronskianRhs (φ ψ : PotPair) (μ ν : ℂ)
    (a b c d : PairVec38) (t : ℝ) : ℂ :=
  2*Complex.I*(μ-ν) *
    wedge (starProd38 (solution φ μ a t) (solution ψ μ c t))
      (starProd38 (solution φ ν b t) (solution ψ ν d t))

end
end NlsGge.GKDefinitionDesign
