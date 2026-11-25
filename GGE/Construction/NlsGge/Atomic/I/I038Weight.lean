import Mathlib
import NlsGge.Atomic.I.I037
import NlsGge.Atomic.I.I020
import NlsGge.Birkhoff.H02Hierarchy38b

                                                                                                           
                                                                                                                 
                                  
                                                                                                            
                                                                                                         
                                                                                                           
                                               
                                                                                                               
                    
                                                                                                                       
                                                                                                
                                                                                                                     
                                                                                                                  
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Birkhoff
open NlsGge.Atomic.I037

namespace NlsGge.ThirdConsultation.I038W

theorem continuous_weight {p : ℝ} (hp : 2 < p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) :
    Continuous (factorialPowerWeight p c) :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_weight (by linarith) hc r).continuousAt

theorem summable_bracket {p : ℝ} (hp : 2 < p) :
    Summable (fun n : ℤ => japaneseBracket n ^ (2 / p - 2)) :=
  summable_bracket_rpow p hp

theorem gap_conjunct (p : ℝ) (hp : 2 < p) (c : BoundedCoefficients 1 2) :
    ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : PhysicalL2, SobolevSquareSummable 1 (physicalFourier u) →
        ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
          |gapRemainderTermE02_38 (factorialPowerWeight p c.val) u n| ≤
            C * factorialPowerWeight p c.val (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n *
              japaneseBracket n ^ (2 / p - 2) := by
  intro B _hB
  have hc : ∀ j, 1 ≤ c.val j ∧ c.val j ≤ 2 := c.property.2.2
  obtain ⟨K, hK, hloc⟩ := actualGapLocalization_allU_E02_38 (max 1 B) (le_max_left _ _)
  obtain ⟨D, hD, hDF⟩ := factorialPower_gap_loss p hp K hK
  refine ⟨D, hD.le, fun u hu hBu n => ?_⟩
  have hn' : ‖physicalSobolevL2 1 u hu‖ ≤ max 1 B := by
    rw [NlsGge.ThirdConsultation.I.i020_norm_eq u hu]; exact hBu.trans (le_max_right _ _)
  have h := abs_gapRemainderTerm_le38 (factorialPowerWeight p c.val) (continuous_weight hp hc) u n
    (D * factorialPowerWeight p c.val (2 * Real.pi * (n : ℝ)) * japaneseBracket n ^ (2 / p - 2))
    (fun l hl => by
      have h1 := hloc u hu hn' n l hl
      have h2 : |l - Real.pi * (n : ℝ)| ≤ K / bracket n := by
        rw [mul_comm Real.pi]; exact h1
      exact hDF c.val hc n l h2)
  refine h.trans (le_of_eq ?_)
  ring

end NlsGge.ThirdConsultation.I038W
