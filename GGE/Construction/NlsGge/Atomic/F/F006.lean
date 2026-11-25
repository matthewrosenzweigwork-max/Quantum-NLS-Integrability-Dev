import Mathlib
import NlsGge.Atomic.F.F006Core
import NlsGge.Atomic.F.F005
import NlsGge.Atomic.G6.G6027
import NlsGge.Atomic.G6.G6028
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore

                                                                                                               
                                                                                                                 
                                                                                                                     
                                                                                                               
                                                     
                                                                                                        
                                                     
                                                                                                                 
                                                                                           
                                                                                                                     
                                                                                                      
                                                                
                                                                                                          
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure

namespace NlsGge.ThirdConsultation.F006Aux

/-- The fixed Birkhoff coordinates of an `H^(m-1)` field lie in `h^(m-1)` (G6027 at level m-1 ≥ 1). -/
theorem physicalBirkhoff_mem (m : ℕ) (hm : 2 ≤ m) (y : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    (NlsGge.GKDefinitionDesign.physicalBirkhoff (sobolevToL2_38 (m - 1) y) : ℤ → ℂ) ∈
      seqSobolev38 ((m - 1 : ℕ) : ℝ) := by
  have hk : 1 ≤ m - 1 := by omega
  have hE := (NlsGge.GKDefinitionDesign.physicalSobolevEmbed_recover (m - 1)).2 _
    (fourierSeq_mem (m - 1) y)
  have h5 := ((NlsGge.GKDefinitionDesign.G6027 (m - 1) hk).2.2.2.2.1
    (NlsGge.GKDefinitionDesign.physicalSobolevRecover (m - 1) (sobolevToL2_38 (m - 1) y))).1
  rwa [hE] at h5

end NlsGge.ThirdConsultation.F006Aux

namespace NlsGge.ThirdConsultation.F

theorem f006 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    (∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ B → ∀ n : ℤ,
          actualGapActionAllE02_38 u n =
            ‖NlsGge.GKDefinitionDesign.physicalBirkhoff u n‖ ^ 2 ∧
          |gapRemainderTermE02_38 (finiteWeightE02_38 m β) u n| ≤
            C * japaneseBracket n ^ (2 * m - 2) *
              ‖NlsGge.GKDefinitionDesign.physicalBirkhoff u n‖ ^ 2) ∧
    (∀ y : SobolevHilbert ((m - 1 : ℕ) : ℝ),
      SobolevSquareSummable ((m - 1 : ℕ) : ℝ)
        (fun n => NlsGge.GKDefinitionDesign.physicalBirkhoff
          (sobolevToL2_38 (m - 1) y) n) ∧
      Summable (fun n : ℤ =>
        |gapRemainderTermE02_38 (finiteWeightE02_38 m β)
          (sobolevToL2_38 (m - 1) y) n|)) := by
  refine ⟨NlsGge.ThirdConsultation.F006Aux.ball_bound m hm β hβ
      (fun u n => NlsGge.GKDefinitionDesign.physicalBirkhoff u n)
      (fun u n => (NlsGge.GKDefinitionDesign.G6028.1 u n).2.2)
      NlsGge.ThirdConsultation.F.F005Aux.exists_weighted_preimage,
    fun y => ⟨(mem_seqSobolev38_iff _ _).1
      (NlsGge.ThirdConsultation.F006Aux.physicalBirkhoff_mem m hm y),
      NlsGge.ThirdConsultation.F006Aux.summable_abs m hm β hβ y⟩⟩

end NlsGge.ThirdConsultation.F
