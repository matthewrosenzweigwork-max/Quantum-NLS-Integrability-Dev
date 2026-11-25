import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38

/- KSPS-032 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS032Host.lean.
   One definition, VERBATIM from followup12 (Pro round 14, 2d599b57) DEFINITIONS/KSPS.lean.md
   "### `NlsGge.ThirdConsultation.KSPS.closedGap`" (round-14 cluster 1 / R14_AUDIT_F2: HOSTABLE; KSPS-032 does not use
   KO.closedGap).  Grep of NlsGge/ (2026-11-01): no `NlsGge.ThirdConsultation.KSPS.closedGap` exists (only KO.closedGap,
   M.closedGap on PhysicalL2).  Owners reused: `SobolevR`, `toPhysical` (KSPS/Round5), `actualGapLowerAllE02_38`,
   `actualGapUpperAllE02_38` (Spectral/ActualLabelledGapActionAllNE02_38, namespace NlsGge.SpectralFoundations).
   Lexical addition only: `open NlsGge.SpectralFoundations` (the owner namespace of the two endpoint names). -/
set_option autoImplicit false
open NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def closedGap (u : SobolevR 1) (n : ℤ) : Set ℝ :=
  Set.Icc
    (actualGapLowerAllE02_38 (toPhysical u) n)
    (actualGapUpperAllE02_38 (toPhysical u) n)

end
end NlsGge.ThirdConsultation.KSPS
