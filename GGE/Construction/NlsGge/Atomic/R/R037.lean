import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.ThirdConsultation.R.R037Support

                                                                                                           
                                                                                                                  
                                                                                        
                                                                                                                    
                                                                                                                 
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

section Step8bDivergence
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

theorem step8b_divergence
    (L : RamerE c s → RamerH c) (ε : ℝ) (hL : Step8Hyp c s hs L ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂(ramerGaussian c s),
        Tendsto (fun j : ℕ => NlsGge.Ramer.ramerJn c s (φ j) hs L x)
          atTop (𝓝 (ramerJac c s hs L x)) := by
  obtain ⟨φ, hφ, hae⟩ := ae_tendsto_ramerA_ramerDiv c s hs L hL.smooth
  exact ⟨φ, hφ, hae.mono fun x hx =>
    tendsto_ramerJn_ramerJac_of_tendsto c s hs L hL.smooth φ hφ x hx⟩

end Step8bDivergence

end
end NlsGge.ThirdConsultation.R
