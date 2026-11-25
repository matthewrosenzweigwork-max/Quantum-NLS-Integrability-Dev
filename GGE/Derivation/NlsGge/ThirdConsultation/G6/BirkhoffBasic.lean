import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.GK38.Lib.InterpolationHilbertOp

/- G6 BirkhoffBasic shared host (proof development, AUTHOR; not reviewed; target NlsGge/ThirdConsultation/G6/BirkhoffBasic.lean).
   Bodies verbatim from followup2 DEFINITIONS/G6.lean.md:29-34 (physicalBirkhoff, physicalInverseBirkhoff). `sourceFamily` is the landed X-006 selection
   (SourceFamilyBasic).  G6.lean.md's other definitions (sequenceSobolevEmbed, ...) are NOT declared here; packets that need them host them separately and must
   import this module rather than redefine these two names (e.g. KSN-020, M-001). -/
set_option autoImplicit false

namespace NlsGge.GKDefinitionDesign
noncomputable section
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

/-- The same physical minus representative selected in X-006. -/
def physicalBirkhoff : PhysicalL2 → Lib.L2Z := sourceFamily.Phi

/-- A total function; its inverse equations are the conclusions of G6-013. -/
def physicalInverseBirkhoff : Lib.L2Z → PhysicalL2 :=
  Function.invFun physicalBirkhoff

end
end NlsGge.GKDefinitionDesign
