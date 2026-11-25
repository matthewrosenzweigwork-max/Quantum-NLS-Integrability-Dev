/- G2-030 production kit (proof development; target NlsGge/Atomic/G2/G2030.lean; #check/#print removed). Source: G2030_PROOF01 (proof development, AUTHOR).
-/
import Mathlib
import NlsGge.GK38.ActionReal

/- G2-030 PROOF01 (proof development, AUTHOR; not self-reviewed). Statement verbatim from STATEMENTS/G2.md G2-030. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G2_030 (u : PhysicalL2) (n : ℤ) :
    gkActionC38 (realSlice u) n = (actualGapActionAllE02_38 u n : ℂ) ∧
    0 ≤ actualGapActionAllE02_38 u n ∧
    (actualGapActionAllE02_38 u n=0 ↔
      actualGapLowerAllE02_38 u n=actualGapUpperAllE02_38 u n) :=
  ⟨action_real_bridge38 u n, action_nonnegative38 u n, action_zero_iff_closed38 u n⟩


end
end NlsGge.GKDefinitionDesign
