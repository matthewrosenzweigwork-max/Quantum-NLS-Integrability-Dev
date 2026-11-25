import Mathlib
import NlsGge.Atomic.G6.G6029Host
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff

/- G6030 HOST PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6030Host.lean.
   Hosts ONCE the G6-030 design name finiteGapTruncationSobolev, body byte-identical to followup13
   DEFINITIONS/G6.lean.md:302-304 (doc comment included), namespace NlsGge.GKDefinitionDesign with the opens of the
   sibling G6029Host (proof development), which hosts truncatePhysicalCoordinates / finiteGapTruncation and deliberately left
   this name for G6-030.  physicalSobolevRecover is imported from the landed G6 SobolevBirkhoff host.  grep NlsGge/
   (2026-11-02): the name does not exist. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped Classical ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- The m-independent truncation is recovered in H^m only after range membership. -/
def finiteGapTruncationSobolev (m N : ℕ) (u : PhysicalL2) :
    PhysicalSobolev38 (m : ℝ) :=
  physicalSobolevRecover m (finiteGapTruncation N u)

end
end NlsGge.GKDefinitionDesign
