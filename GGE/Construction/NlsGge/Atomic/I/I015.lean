import Mathlib
import NlsGge.Spectral.ActualFirstMomentE02_38
import NlsGge.Spectral.ActualGapActionAllNE02_38

                                                                                                                   
                                                                                                                     
                                                                                                                        
                                                                                                             
                                 

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis
open NlsGge.SpectralFoundations

namespace NlsGge.Atomic.I015

theorem finiteGap_firstSpectralMoment
    (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ |
      actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite) :
    Integrable (fun x : ℝ => (2*x) * actualGapHeightE02_38 u x) ∧
    Summable (fun n : ℤ => (2*Real.pi*n) * actualGapActionAllE02_38 u n) ∧
    (2/Real.pi) * (∫ x : ℝ, (2*x) * actualGapHeightE02_38 u x) =
      ∑ n ∈ hfin.toFinset, (2*Real.pi*n) * actualGapActionAllE02_38 u n := by
  obtain ⟨h1, h2, h3⟩ := actualFirstMoment_eq_sum_E02_38 u hu hfin
  have hzero : ∀ n : ℤ, n ∉ hfin.toFinset → (2*Real.pi*n) * actualGapActionAllE02_38 u n = 0 := by
    intro n hn
    have hEq := (actualGapLevelSet_eq_Icc_E02_38 u n).2
    have hne : (actualGapLevelSetE02_38 u n).Nonempty := (actualGapLevelSet_eq_Icc_E02_38 u n).1
    have hle : actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
      rw [hEq] at hne
      exact Set.nonempty_Icc.1 hne
    have hnot : ¬ actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n := by
      intro hlt
      exact hn ((Set.Finite.mem_toFinset hfin).2 hlt)
    have heq : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n :=
      le_antisymm hle (not_lt.1 hnot)
    unfold actualGapActionAllE02_38
    rw [heq, intervalIntegral.integral_same, mul_zero, mul_zero]
  have hts : ∑' n : ℤ, 2*Real.pi*n * actualGapActionAllE02_38 u n =
      ∑ n ∈ hfin.toFinset, (2*Real.pi*n) * actualGapActionAllE02_38 u n := by
    apply tsum_eq_sum
    intro n hn
    exact hzero n hn
  refine ⟨h1, h2, ?_⟩
  rw [h3, hts]

end NlsGge.Atomic.I015
