import NlsGge.GK38.EigenvalueCompactnessHeight
import NlsGge.Birkhoff.BirkhoffAPI38

set_option autoImplicit false
open MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

/-- Unconditional real-action nonnegativity, reusing the accepted scalar estimate. -/
theorem actionNonnegative38 (u : PhysicalL2) (n : ℤ) :
    0 ≤ actualGapActionAllE02_38 u n := by
  exact le_trans (div_nonneg (sq_nonneg _) (by norm_num))
    (actualGapAction_ge_sq_div_four_all_E02_38 u n)

/-- Zero action characterizes exactly a collapsed actual labelled interval. -/
theorem actionZeroIffClosed38 (u : PhysicalL2) (n : ℤ) :
    actualGapActionAllE02_38 u n = 0 ↔
      actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n := by
  constructor
  · intro h
    exact (NlsGge.Birkhoff.actualGap_closed_of_action_eq_zero38 u n h).symm
  · intro h
    have _height_integrable := gapAction_intervalIntegrable_L2_38 u n
    simp only [actualGapActionAllE02_38, h, intervalIntegral.integral_same, mul_zero]

/-- Strictly positive action characterizes strict ordering of the actual endpoints. -/
theorem actionPositiveIffOpen38 (u : PhysicalL2) (n : ℤ) :
    0 < actualGapActionAllE02_38 u n ↔
      actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n := by
  constructor
  · intro h
    rcases lt_or_eq_of_le (NlsGge.Birkhoff.actualGapLower_le_upper38 u n) with hopen | hclosed
    · exact hopen
    · have hz := (actionZeroIffClosed38 u n).mpr hclosed
      linarith
  · exact NlsGge.Birkhoff.actualGapAction_pos_of_open38 u n

end
end NlsGge.GK38
