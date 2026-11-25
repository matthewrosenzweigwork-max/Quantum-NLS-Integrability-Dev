import Mathlib
import NlsGge.Atomic.R.R022
import NlsGge.Atomic.R.R025

                                                                                                  
                                                                                    
                                                                                                      
                                                                                                                
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section
section R028G1
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

include hs in
/-- G1: local bump with a closed divergence. For a `C²` field `K` and a point `x₀` there are a radius
`r > 0` and a bounded `C²` field `G` with `G = K` on `ball x₀ r`, and `G` has a closed divergence. -/
theorem r028_exists_bump (K : RamerE c s → RamerH c) (hK : ContDiff ℝ 2 K) (x₀ : RamerE c s) :
    ∃ r : ℝ, 0 < r ∧ ∃ G : RamerE c s → RamerH c, ContDiff ℝ 2 G ∧
      EqOn G K (ball x₀ r) ∧ BoundedFieldAndDerivative G ∧
      ∃ e : RamerE c s → ℝ, IsClosedDiv c s G e := by
  obtain ⟨r, hr, G, hG, hEq, hB⟩ := r022_exists_bumped_field K hK x₀
  obtain ⟨e, he⟩ := exists_isClosedDiv_of_bounded c s hs G hG hB
  exact ⟨r, hr, G, hG, hEq, hB, e, he⟩

end R028G1
end
end NlsGge.ThirdConsultation.R
