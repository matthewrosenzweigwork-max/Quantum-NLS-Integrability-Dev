import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import Armstrong.Work.RawBetaSum

/- G3-003 HOST (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/ThirdConsultation/G3/G3003Host.lean.
   Hosts the design name `offDiagonalBeta`, body VERBATIM from DEFINITIONS/G3.lean.md:35-38 (followup7).
   Its body is the Armstrong constant `NlsGge.GK38.gk151BetaAmbient38` (Armstrong/Work/RawBetaSum.lean), which lies INSIDE the approved
   X-006 closure (Armstrong.Work.RawBetaSum is line 85 of root/X006_ARMSTRONG_BASE_MODULES01.txt and is a transitive import of
   Armstrong.Work.ActualPhysicalSmallBallFiniteGap, hence of NlsGge.Atomic.X.X006).  So no copy is needed (a copy under the same name
   would clash with the in-closure constant); the explicit import is within the closure, per root decision 8.
   Shared host: later G3 packets mentioning offDiagonalBeta import this module and must not redeclare it. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def offDiagonalBeta (n m : ℤ) : PotPair → ℂ :=
  gk151BetaAmbient38 sourceW sourceFamily.W_open sourceFamily.W_real
    sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
    sourceFamily.F_period n m

end
end NlsGge.GKDefinitionDesign
