import Mathlib
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.ThirdConsultation.T.ECarrier98
import NlsGge.ThirdConsultation.T.TDefsHost
import NlsGge.ThirdConsultation.T.TDefs2Host
import NlsGge.Atomic.T.T010
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Birkhoff.F11Claim38d
import NlsGge.Sobolev38.SobolevCarrier38

/- T-011 PRODUCTION02 (codex_luna12, AUTHOR; not compiled or reviewed).
   Target: NlsGge/Atomic/T/T011.lean.
   Head copied verbatim from followup13 STATEMENTS/T.md §T-011; round 17 keeps
   the head unchanged. The proof composes bounded continuous tests with the
   actual ordinarySobolev carrier map and applies landed T-010. -/

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open scoped BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.T
noncomputable section

theorem fullFourier_weak_all_fixedSobolev
    (lo up : ℝ) (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4)
    (r : ℝ) (hr : 0 ≤ r) :
    ∀ F : SobolevHilbert r →ᵇ ℝ,
      Tendsto (fun N : ℕ => ∫ x, F (ordinarySobolev c s r x)
        ∂fullFourierLawE c s N) atTop
        (𝓝 (∫ x, F (ordinarySobolev c s r x) ∂muWE c s hs hs')) := by
  intro F
  have hOrdinary : Continuous (ordinarySobolev c s r) := by
    unfold ordinarySobolev
    exact ((continuous_ofCarrier38 r).comp (continuous_reflCF11_38 r)).comp
      (continuous_eToSob38 c s r)
  simpa only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] using
    ((fullFourier_weak_weighted lo up c s hs hs').2.2
      (F.compContinuous ⟨ordinarySobolev c s r, hOrdinary⟩))

end
end NlsGge.ThirdConsultation.T
