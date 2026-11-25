import Mathlib
import NlsGge.Atomic.I.I017Core
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.Atomic.G6.G6013

/- I ACTUAL-INVERSE BRIDGE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe).
   Target NlsGge/ThirdConsultation/I/ActualInverseBridge.lean, namespace NlsGge.ThirdConsultation.I.
   Round-14 bridge head `actual_inverse_eq_physicalOfSequence` verbatim (followup13 STATEMENTS/I.md, "Round-14 I/T/PDE/F
   bridges"; Pro: "put inverse ... bridges in I's shared host after the concrete realization"), with its one support
   lemma physicalInverseBirkhoff_zero.  Proof: lane-checked core I017C.cleanΦinv_eq_of, discharged by the landed
   PDE.actualBirkhoffTop38_cleanPhiInv (h⁰ branch) and G6013's left inverse at Φ(0) = 0 (I017C.physicalBirkhoff_zero;
   the off-h⁰ branch of both maps is the field 0).  All-sequence equality, as Pro requires; no a.e. statement here. -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

/-- `Φ⁻¹(0) = 0` for the selected physical inverse (G6-013 left inverse at `Φ(0) = 0`). -/
theorem physicalInverseBirkhoff_zero : physicalInverseBirkhoff 0 = 0 := by
  have h := G6013.2.2.2.2.1 (0 : PhysicalL2)
  rwa [NlsGge.ThirdConsultation.I017C.physicalBirkhoff_zero] at h

theorem actual_inverse_eq_physicalOfSequence (z : ℤ → ℂ) :
    PDE.actualBirkhoffTop38.cleanΦinv z = I.physicalOfSequence z :=
  NlsGge.ThirdConsultation.I017C.cleanΦinv_eq_of PDE.actualBirkhoffTop38
    (fun z hz => PDE.actualBirkhoffTop38_cleanPhiInv z hz) physicalInverseBirkhoff_zero z

end NlsGge.ThirdConsultation.I
