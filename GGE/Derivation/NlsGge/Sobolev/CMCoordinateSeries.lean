import NlsGge.Sobolev.RealBasis
import NlsGge.Sobolev.CMWeightComparison
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NlsGge.Pilot
open NlsGge.Pilot
variable {lower upper : ℝ}
theorem cm_norm_coordinate_series
    (c : BoundedCoefficients lower upper) (s : ℝ) (hs : 0 ≤ s)
    (x : WeightedRealHilbert (cmModeWeight c)) :
    ‖cmToFullWeightedHilbert c s hs x‖ ^ 2 =
      ∑' n : ℤ, fullModeWeight c s n *
        ‖(show WeightedHilbert (cmModeWeight c) from x) n‖ ^ 2 := by
  calc
    ‖cmToFullWeightedHilbert c s hs x‖ ^ 2 =
        ∑' n : ℤ, fullModeWeight c s n *
          ‖(show WeightedHilbert (fullModeWeight c s) from
            cmToFullWeightedHilbert c s hs x) n‖ ^ 2 := by
      change ‖(show WeightedHilbert (fullModeWeight c s) from
        cmToFullWeightedHilbert c s hs x)‖ ^ 2 = _
      exact weightedHilbert_norm_sq (fullModeWeight c s)
        (show WeightedHilbert (fullModeWeight c s) from cmToFullWeightedHilbert c s hs x)
    _ = _ := by
      apply tsum_congr
      intro n
      exact congrArg (fun z : ℂ => fullModeWeight c s n * ‖z‖ ^ 2)
        (cmToFullWeightedHilbert_apply c s hs x n)
end NlsGge.Pilot
