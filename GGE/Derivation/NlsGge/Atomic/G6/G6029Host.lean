import Mathlib
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.GK38.Lib.InterpolationTail

/- G6029 HOST PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6029Host.lean.
   Hosts ONCE the two G6-029 design names (R14_AUDIT_B row G6-029: "Hosts finiteGapTruncation"): truncatePhysicalCoordinates
   and finiteGapTruncation, bodies byte-identical to followup13 DEFINITIONS/G6.lean.md, namespace NlsGge.GKDefinitionDesign
   with that file's opens. finiteGapTruncationSobolev (G6-030) is NOT hosted here. grep NlsGge/ (2026-11-02): neither name
   exists. physicalBirkhoff / physicalInverseBirkhoff are imported from G6.BirkhoffBasic; Lib.win from GK38.Lib. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped Classical ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Symmetric truncation includes n=0 for every N. -/
def truncatePhysicalCoordinates (N : ℕ) (z : Lib.L2Z) : Lib.L2Z :=
  ∑ n ∈ Lib.win N, lp.single 2 n (z n)

def finiteGapTruncation (N : ℕ) (u : PhysicalL2) : PhysicalL2 :=
  physicalInverseBirkhoff (truncatePhysicalCoordinates N (physicalBirkhoff u))

end
end NlsGge.GKDefinitionDesign
