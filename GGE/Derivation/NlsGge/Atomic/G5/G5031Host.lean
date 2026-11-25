import Mathlib
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.Atomic.G5.G5017Host

/- G5-031 HOST (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5031Host.lean.
   Hosts `anglePoisson` and `doubleAngleDiscriminantBracket`.  Bodies are byte-identical extractions from followup12
   DEFINITIONS/G5.lean.md lines 99-104 (round 14), with the single lexical repair of the binder `λ` to `lam` (licensed by Pro round 14,
   "License the uniform λ→lam ... including doubleAngleDiscriminantBracket").  Names grepped absent from NlsGge/ (2026-11-01).
   Shared host: G5-030, G5-032, G5-035, G5-036, G5-038 import this module and must not redeclare these names.
   `pairPoisson` is landed in G5017Host, `pairPoissonCLM`/`angleDerivative` in G5033Host. -/
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def anglePoisson (m n : ℤ) (φ : PotPair) : ℂ :=
  pairPoissonCLM (angleDerivative m φ) (angleDerivative n φ)

def doubleAngleDiscriminantBracket (m n : ℤ) (φ : PotPair) (lam : ℂ) : ℂ :=
  pairPoisson (fun ψ => discrim ψ lam) (anglePoisson m n) φ

end
end NlsGge.GKDefinitionDesign
