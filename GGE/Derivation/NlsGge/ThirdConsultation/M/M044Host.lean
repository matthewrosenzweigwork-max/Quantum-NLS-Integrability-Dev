import Mathlib
import NlsGge.Atomic.M.M001

/- M-044 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/M/M044Host.lean, namespace NlsGge.ThirdConsultation.M.
   Hosts ONLY `oddTraceSum` (body verbatim from followup13 DEFINITIONS/M.lean.md L345-346, retained, not in the round-14
   removal list) and `oddTraceEnergy` (verbatim from L1988-1989).  grep NlsGge/ and Work/ (2026-11-02): neither declared. -/
set_option autoImplicit false
open scoped ENNReal
open NlsGge.Pilot

namespace NlsGge.ThirdConsultation.M
noncomputable section

def oddTraceSum (m : ℕ) (u : PhysicalL2) : ℝ :=
  ∑' n : ℤ, 4^m * higherAction u n (2*m+1)

def oddTraceEnergy (m : ℕ) (u : PhysicalL2) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal ((4 : ℝ) ^ m * higherAction u n (2 * m + 1))

end
end NlsGge.ThirdConsultation.M
