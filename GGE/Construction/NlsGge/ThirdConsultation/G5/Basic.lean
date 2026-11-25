import Mathlib
import NlsGge.GK38.Lib.InterpolationLemma

                                                                             
                                                                                                                                           
set_option autoImplicit false
noncomputable section
open NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

def canonicalProduct (σ : ℤ → ℂ) (z : ℂ) : ℂ := -Lib.psiProd σ z

def cardinalProduct (σ : ℤ → ℂ) (j : ℤ) (z : ℂ) : ℂ :=
  ∏'[SummationFilter.symmetricIcc ℤ] k : ℤ,
    (if k = j then 1 else (σ k - z) / (σ k - σ j))

end NlsGge.GKDefinitionDesign
