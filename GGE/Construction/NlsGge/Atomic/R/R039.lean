import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.RamerStep8Bridge

                                                                                                           
                                                                                                                        
                                                                                                                            
                                                                                                                      
                        
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section
section R039Main
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "J" => ramerJac c s hs
local notation "Smap" => TM c s hs

/-- **R-039, null pullback on the same local chart** (Pro round 6 head, verbatim). -/
theorem step8c_null
    (L : E → H) (ε : ℝ) (hL : Step8Hyp c s hs L ε) :
    (∀ᵐ x ∂μ, x ∈ localDomain c s ε → 0 < J L x) ∧
    NullPreservingOn μ (Smap L)
      (localDomain c s ε ∩
        (Smap L) ⁻¹' ball (0 : E) (ε / 2)) :=
  by
  have hprod := NlsGge.Ramer.step8c_ramerJac c s hs L hL
  have key : ∀ x : E, ramerJac c s hs L x = NlsGge.Ramer.ramerJac c s hs L x :=
    fun x => (NlsGge.Ramer.ramerJac_eq c s hs L x).symm
  refine ⟨?_, ?_⟩
  · filter_upwards [hprod.1] with x hx hxB
    rw [key]
    exact hx hxB
  · intro A hA
    have hA' : μ (ball (0 : E) (ε / 2) ∩ A) = 0 :=
      measure_mono_null Set.inter_subset_right hA
    have hMm : MeasurableSet
        (toMeasurable μ (ball (0 : E) (ε / 2) ∩ A) ∩ ball (0 : E) (ε / 2)) :=
      (measurableSet_toMeasurable μ _).inter measurableSet_ball
    have hM0 : μ (toMeasurable μ (ball (0 : E) (ε / 2) ∩ A) ∩ ball (0 : E) (ε / 2)) = 0 :=
      measure_mono_null Set.inter_subset_left
        (by rw [measure_toMeasurable]; exact hA')
    have h3 := hprod.2.2 _ hMm Set.inter_subset_right hM0
    refine measure_mono_null ?_ h3
    intro x hx
    obtain ⟨⟨hxc, hxB⟩, hxA⟩ := hx
    have hmem : (Smap L x) ∈ ball (0 : E) (ε / 2) ∩ A := ⟨hxB, hxA⟩
    exact ⟨hxc, ⟨subset_toMeasurable μ _ hmem, hxB⟩⟩

end R039Main
end
end NlsGge.ThirdConsultation.R
