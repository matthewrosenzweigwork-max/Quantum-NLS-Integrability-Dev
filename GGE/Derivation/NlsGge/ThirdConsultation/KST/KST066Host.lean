import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.GK38.Lib.InterpolationHilbertOp
import NlsGge.Sobolev.PeriodicBridge

/- KST066Host HOST01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST066Host.lean.
   SUPPORTING host module (no packet increment).  Bodies VERBATIM from design DEFINITIONS/KST.lean.md lines 514-523
   ("Fractional real Sobolev embedding, shared with KSN"; identical in gpt6pro_followup9/10; Pro rounds 11-12 do not touch it):
   sequenceSobolevEmbedRealExponent, physicalSobolevEmbedRealExponent, namespace NlsGge.GKDefinitionDesign.
   Neither is defined anywhere in NlsGge (grep) nor in another worker's candidate; KSN (inverseSmoothing etc.), DM.lean.md:346
   and KST-066 consume them.  Opens exactly as the design block.  No repair. -/
set_option autoImplicit false
noncomputable section

namespace NlsGge.GKDefinitionDesign
open NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common
open NlsGge.Pilot NlsGge.GK38

def sequenceSobolevEmbedRealExponent (s : ℝ) (hs : 0 ≤ s)
    (z : SobolevCarrier38 s) : Lib.L2Z :=
  let z0 := carrierIncl38 (r := 0) (s := s) hs z
  seqToLp38 (carrierCoe38 0 z0) (carrierCoe38_mem 0 z0)

def physicalSobolevEmbedRealExponent (s : ℝ) (hs : 0 ≤ s)
    (u : PhysicalSobolev38 s) : PhysicalL2 :=
  reflectedFourierL2.symm (sequenceSobolevEmbedRealExponent s hs
    (physicalSobolevFourierEquiv38 s u))

end NlsGge.GKDefinitionDesign
end
