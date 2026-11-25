import Mathlib
import NlsGge.ThirdConsultation.G5033Host

/- G5-017 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5017Host.lean.
   Hosts pairGradient, pairHamiltonianField, pairPoisson. Bodies are byte-identical extractions from Pro round 9
   (root/gpt6pro_followup7 DEFINITIONS/G5.lean.md lines 28-38). pairGradientCLM and pairPoissonCLM are NOT redefined: they are
   landed in NlsGge.ThirdConsultation.G5033Host (imported). Names grepped absent from NlsGge/ and from Work/isolated_20261027
   worker folders (2026-10-31). Armstrong imports reach only through G5033Host (Armstrong.Work.ActualCartesianXYModels, in the X-006 closure). -/
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def pairGradient (f : PotPair → ℂ) (φ : PotPair) : PotPair :=
  pairGradientCLM (fderiv ℂ f φ)

def pairHamiltonianField (g : PotPair → ℂ) (φ : PotPair) : PotPair :=
  (-Complex.I • (pairGradient g φ).2, Complex.I • (pairGradient g φ).1)

def pairPoisson (f g : PotPair → ℂ) (φ : PotPair) : ℂ :=
  fderiv ℂ f φ (pairHamiltonianField g φ)

end
end NlsGge.GKDefinitionDesign
