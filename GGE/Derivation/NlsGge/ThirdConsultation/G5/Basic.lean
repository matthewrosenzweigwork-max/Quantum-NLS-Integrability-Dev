import Mathlib
import NlsGge.GK38.Lib.InterpolationLemma

/- G5 host (proof development draft). Target NlsGge/ThirdConsultation/G5/Basic.lean.
   canonicalProduct and cardinalProduct copied verbatim from DEFINITIONS/G5.lean.md lines 129-134 (namespace NlsGge.GKDefinitionDesign). -/
set_option autoImplicit false
noncomputable section
open NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

def canonicalProduct (σ : ℤ → ℂ) (z : ℂ) : ℂ := -Lib.psiProd σ z

def cardinalProduct (σ : ℤ → ℂ) (j : ℤ) (z : ℂ) : ℂ :=
  ∏'[SummationFilter.symmetricIcc ℤ] k : ℤ,
    (if k = j then 1 else (σ k - z) / (σ k - σ j))

end NlsGge.GKDefinitionDesign
