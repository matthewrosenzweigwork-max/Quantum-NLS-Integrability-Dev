import NlsGge.ThirdConsultation.KST.KST066Host
import NlsGge.ThirdConsultation.G6.BirkhoffBasic

/- KSN022Host HOST01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/KSN/KSN022Host.lean.  SUPPORTING host module (no packet increment).
   Body VERBATIM from followup13 DEFINITIONS/KSN.lean.md (sha256 865a3ac2...) lines 346-349, section
   "Real restrictions at arbitrary exponents", namespace NlsGge.GKDefinitionDesign:
     birkhoffSobolevRealExponent  (round-14 audit C: "HOSTABLE birkhoffSobolevRealExponent (DEF KSN 224)").
   Uses physicalSobolevEmbedRealExponent from the landed KST066Host and G6's single physicalBirkhoff (BirkhoffBasic).
   Only the one name consumed by KSN-022 is hosted; physicalSobolevRecoverRealExponent,
   inverseBirkhoffSobolevRealExponent and inverseSmoothing (same design block) belong to the KSN-021/023 hosts.
   Opens as the landed G6 SobolevBirkhoff host (the dependent `if` needs classical decidability).  No repair.
   The `else 0` branch is shown unused by KSN022Asm (membership is earned before the carrier is formed). -/
set_option autoImplicit false
noncomputable section
open scoped Classical
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

def birkhoffSobolevRealExponent (s : ℝ) (hs : 0 ≤ s) (u : PhysicalSobolev38 s) :
    SobolevCarrier38 s :=
  let z : ℤ → ℂ := physicalBirkhoff (physicalSobolevEmbedRealExponent s hs u)
  if h : z ∈ seqSobolev38 s then carrierMk38 s z h else 0

end NlsGge.GKDefinitionDesign

end
