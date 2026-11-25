import Mathlib
import NlsGge.ThirdConsultation.G5.Basic
import NlsGge.Atomic.G5.G5024
import NlsGge.GK38.Lib.InterpolationLemma

                                                                                                                                   
                                                                                                                                          
                                                                                                                                  
set_option autoImplicit false

open Set Filter Topology
open NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5023 (σ : ℤ → ℂ) (f : ℂ → ℂ) (z : ℂ)
    (hσ : Summable (fun k : ℤ => ‖σ k - (k : ℂ) * Real.pi‖^2))
    (hinj : Function.Injective σ) (hf : Differentiable ℂ f)
    (hdecay : CircleRatioTendstoZero f Complex.sin) :
  (∀ j : ℤ, Multipliable (fun k : ℤ => if k = j then 1 else
    (σ k-z)/(σ k-σ j)) (SummationFilter.symmetricIcc ℤ)) ∧
  HasSum (fun j : ℤ => f (σ j) * cardinalProduct σ j z) (f z)
    (SummationFilter.symmetricIcc ℤ) ∧
  Tendsto (fun R : ℕ => ∑ j ∈ Lib.win R, f (σ j) * cardinalProduct σ j z)
    atTop (𝓝 (f z)) := by
  obtain ⟨h1, h2, h3⟩ := Lib.interpolation_lemma hf hdecay hσ hinj z
  have hS : HasSum (fun j : ℤ => f (σ j) * cardinalProduct σ j z) (f z)
      (SummationFilter.symmetricIcc ℤ) := by
    have := h2.hasSum
    rw [← h3] at this
    exact this
  refine ⟨h1, hS, ?_⟩
  have := (SummationFilter.hasSum_symmetricIcc_iff).1 hS
  exact this

end
end NlsGge.GKDefinitionDesign
