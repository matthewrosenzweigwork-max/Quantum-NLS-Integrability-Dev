import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.RamerLocalLowerBound
import NlsGge.Ramer.RamerStep10

                                                                                                           
                                                                                                             
                                                                                                                   
                                                                                                                    
                                                                                                                   
                                                                                                           
                                                                                             
                                                                                                                         
                                                                                                             
                                                                                                                         
                                                                                                                         
                                                                                                                      
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

section R046Production
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "i" => cmEmbedding c s hs

theorem local_null_preserving
    (T : E ≃ₜ E) (K Kinv : E → H)
    (hT : RamerHomeomorphismData c s hs T K Kinv) :
    ∀ x₀ : E, ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧
      NullPreservingOn μ T U := by
  obtain ⟨hK, hKi, hTK, hTKi⟩ := hT
  have hT' : ∀ x : E, T x = x + i (K x) := fun x => hTK x
  have hTi' : ∀ y : E, T.symm y = y + i (Kinv y) := fun y => hTKi y
  intro x₀
  have hU1 : IsUnit (1 + (hsDerivH c s hs K x₀).toCLM) :=
    (NlsGge.Ramer.step10_isUnit c s hs T K Kinv hT' hTi'
      (hK.of_le (by norm_num)) (hKi.of_le (by norm_num)) x₀).1
  obtain ⟨V, hVo, hxV, -, -, hnull⟩ :=
    NlsGge.Ramer.ramer_local_lower_bound c s hs K hK x₀ hU1
  refine ⟨V, hVo, hxV, fun A hA => ?_⟩
  have hTf : (fun y => y + NlsGge.Ramer.inclE c s hs (K y)) = ⇑T := (funext hT').symm
  have h := hnull A hA
  rw [hTf] at h
  exact h

end R046Production

end
end NlsGge.ThirdConsultation.R
