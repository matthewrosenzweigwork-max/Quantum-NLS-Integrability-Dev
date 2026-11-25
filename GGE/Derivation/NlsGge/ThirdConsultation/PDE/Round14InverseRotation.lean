import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14Rotation
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff
import NlsGge.ThirdConsultation.Common.FiniteSupport

/- PDEINVROT HOST PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target
   NlsGge/ThirdConsultation/PDE/Round14InverseRotation.lean, namespace NlsGge.ThirdConsultation.PDE.
   Hosts ONCE the remainder of the Pro r14 shared PDE block l.2765-2772 (PRO_DEFINITION_RESPONSE_FP80_14.md):
   inverseRotationCurve, inverseRotationPhysical. Bodies VERBATIM. proof development's Round14Rotation (PDEROT host) hosts the
   preceding l.2738-2764 and explicitly leaves these two to PDE-064. Prelude = Pro's r14 block prelude (l.2642-2649).
   ROOT LEXICAL REPAIR 22 (binder type, as in PDEROT): `Lib.L2Z` -> `NlsGge.GK38.Lib.L2Z` in the two binders.
   No other change. MAIN-ONLY through Round14Rotation -> Round14ActionFreq (G6041 closure). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.NLS38 NlsGge.GKDefinitionDesign NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def inverseRotationCurve (z0 : NlsGge.GK38.Lib.L2Z)
    (hz : FiniteSupportSequence z0) (t : ℝ) :
    PhysicalSobolev38 ((3 : ℕ) : ℝ) :=
  inverseBirkhoffSobolev 3 (rotationCurve ((3 : ℕ) : ℝ) z0 hz t)

def inverseRotationPhysical (z0 : NlsGge.GK38.Lib.L2Z)
    (hz : FiniteSupportSequence z0) (t : ℝ) : PhysicalL2 :=
  physicalSobolevEmbed 3 (inverseRotationCurve z0 hz t)

end
end NlsGge.ThirdConsultation.PDE
