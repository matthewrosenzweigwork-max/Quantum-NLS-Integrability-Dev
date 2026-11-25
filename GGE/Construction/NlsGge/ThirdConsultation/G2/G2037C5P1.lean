import Mathlib
import NlsGge.Atomic.G2.G2046
import NlsGge.ThirdConsultation.G2.G2037Host

                                                                                                    
                                                                                                 
                                                                                                      
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Step (a) of conjunct (5): the cuts of a finite index set lie in a closed ball about 0 of positive radius. -/
theorem g2037c5_cuts_bounded (u : PhysicalL2) (S : Finset ℤ) :
    ∃ R : ℝ, 0 < R ∧ finiteGapCuts u S ⊆ Metric.closedBall (0 : ℂ) R := by
  have hb : Bornology.IsBounded (finiteGapCuts u S) := by
    unfold finiteGapCuts
    refine (Bornology.isBounded_biUnion S.finite_toSet).2 ?_
    intro n _
    unfold gapSegment
    rw [← convexHull_pair]
    exact ((Set.toFinite ({lamMinus (realSlice u) n, lamPlus (realSlice u) n} : Set ℂ)).isCompact_convexHull
      (𝕜 := ℝ)).isBounded
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hb
  exact ⟨max r 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩

end
end NlsGge.GKDefinitionDesign
