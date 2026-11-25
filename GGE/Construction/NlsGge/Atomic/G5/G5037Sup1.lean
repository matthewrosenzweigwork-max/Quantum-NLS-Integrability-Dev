import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5029Host
import NlsGge.Atomic.G5.G5029Sup3
import NlsGge.Atomic.G5.G5FlowBridge
import NlsGge.Atomic.G5.G5036
import NlsGge.Atomic.G1.G1081
import NlsGge.Atomic.G1.G1082
import NlsGge.Atomic.G1.G1082Sup5
import NlsGge.Atomic.G1.G1083
import NlsGge.ThirdConsultation.KO.Basic

                                                                                       
                                                                                         
                                                                                                                                
                                                                                                                             
                                                                                                                              
                                                                                                                               
                                                                                                                                     
                                                                                                                               
                                                                                                                                      
                                                                                                                                
                                                                                                                               
                                         
                                                                                                                               
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G5037Sup1
noncomputable section

/-- At a collapsed gap the Dirichlet point is the left endpoint. -/
theorem gkMu_eq_lower_of_not_lt (u : PhysicalL2) (j : ℤ)
    (h : ¬ actualGapLowerAllE02_38 u j < actualGapUpperAllE02_38 u j) :
    gkMu u j = actualGapLowerAllE02_38 u j := by
  have hmem := gkMu_mem_gap38 u j
  exact le_antisymm (hmem.2.trans (not_lt.mp h)) hmem.1

theorem core37_finset (m n : ℤ)
    (h30 : ∀ (u : PhysicalL2) (m n : ℤ), AllDirichletLeft u →
      gamma2 (realSlice u) m ≠ 0 → gamma2 (realSlice u) n ≠ 0 →
      anglePoisson m n (realSlice u) = 0)
    (F : Finset ℤ) :
    ∀ u : PhysicalL2, (∀ j : ℤ, j ∉ F → gkMu u j = actualGapLowerAllE02_38 u j) →
      gamma2 (realSlice u) m ≠ 0 → gamma2 (realSlice u) n ≠ 0 →
      anglePoisson m n (realSlice u) = 0 := by
  induction F using Finset.induction_on with
  | empty =>
    intro u hleft hm hn
    exact h30 u m n (fun j => hleft j (Finset.notMem_empty j)) hm hn
  | insert a F ha ih =>
    intro u hleft hm hn
    by_cases ho : actualGapLowerAllE02_38 u a < actualGapUpperAllE02_38 u a
    · obtain ⟨t, ht⟩ := exists_flow_hit a u _ (left_datum_mem_gapCircle u a ho)
      obtain ⟨-, hcomp, -, -, hiso⟩ := G1_081 a
      have hflow := completeGapFlow_isSpectralFlow a (singleGapFlow a) hcomp u
      have hm0 : gamma2 (realSlice ((fun s : ℝ => singleGapFlow a s u) 0)) m ≠ 0 := by
        show gamma2 (realSlice (singleGapFlow a 0 u)) m ≠ 0
        rw [hcomp.1 u]
        exact hm
      have hn0 : gamma2 (realSlice ((fun s : ℝ => singleGapFlow a s u) 0)) n ≠ 0 := by
        show gamma2 (realSlice (singleGapFlow a 0 u)) n ≠ 0
        rw [hcomp.1 u]
        exact hn
      obtain ⟨hmt, hnt, heq⟩ := G5036 a m n (fun s : ℝ => singleGapFlow a s u) hflow hm0 hn0 t
      have hmt' : gamma2 (realSlice (singleGapFlow a t u)) m ≠ 0 := hmt
      have hnt' : gamma2 (realSlice (singleGapFlow a t u)) n ≠ 0 := hnt
      have heq' : anglePoisson m n (realSlice (singleGapFlow a t u)) =
          anglePoisson m n (realSlice (singleGapFlow a 0 u)) := heq
      rw [hcomp.1 u] at heq'
      have hisov : isospectral u (singleGapFlow a t u) := hiso t u
      have hleftv : ∀ j : ℤ, j ∉ F →
          gkMu (singleGapFlow a t u) j = actualGapLowerAllE02_38 (singleGapFlow a t u) j := by
        intro j hj
        rw [isospectral_gapLower_eq hisov j]
        by_cases hja : j = a
        · subst hja
          have h1 := congrArg Prod.fst ht
          exact h1
        · rw [(G1_082 a u).1 j hja t]
          exact hleft j (by simp [hja, hj])
      rw [← heq']
      exact ih (singleGapFlow a t u) hleftv hmt' hnt'
    · refine ih u (fun j hj => ?_) hm hn
      by_cases hja : j = a
      · subst hja
        exact gkMu_eq_lower_of_not_lt u j ho
      · exact hleft j (by simp [hja, hj])

/-- GK 18.7: on a finite-gap potential the angle bracket vanishes, given G5-030 (parameter `h30`). -/
theorem core37 (u : PhysicalL2) (m n : ℤ) (hfg : NlsGge.ThirdConsultation.finiteGap u)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0)
    (h30 : ∀ (u : PhysicalL2) (m n : ℤ), AllDirichletLeft u →
      gamma2 (realSlice u) m ≠ 0 → gamma2 (realSlice u) n ≠ 0 →
      anglePoisson m n (realSlice u) = 0) :
    anglePoisson m n (realSlice u) = 0 := by
  refine core37_finset m n h30 (Set.Finite.toFinset hfg) u (fun j hj => ?_) hm hn
  have hj' : ¬ (actualGapLowerAllE02_38 u j ≠ actualGapUpperAllE02_38 u j) := fun h =>
    hj ((Set.Finite.mem_toFinset hfg).2 h)
  exact gkMu_eq_lower_of_not_lt u j (fun hlt => hj' hlt.ne)

end
end G5037Sup1
end NlsGge.GKDefinitionDesign
