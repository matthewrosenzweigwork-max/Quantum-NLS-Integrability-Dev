import Mathlib
import NlsGge.ThirdConsultation.G6.Round5
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff

/- G6033 HOST PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6033Host.lean.
   Hosts ONCE the G6-033 design name transformedNLSHamiltonian (R14_AUDIT_B row G6-033: "HOSTABLE ... hosts
   transformedNLSHamiltonian"), body byte-identical to followup13 DEFINITIONS/G6.lean.md:144-145 (carrier index
   ((1 : ℕ) : ℝ) per Pro r14 "Carrier index casts").  nlsHamiltonian is the landed ThirdConsultation/G6/Round5 one
   (Pro r14: reused, not redeclared); inverseBirkhoffSobolev from the landed G6 SobolevBirkhoff host.
   grep NlsGge/ (2026-11-02): the name does not exist. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

def transformedNLSHamiltonian (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) : ℝ :=
  nlsHamiltonian (inverseBirkhoffSobolev 1 z)

end
end NlsGge.GKDefinitionDesign
