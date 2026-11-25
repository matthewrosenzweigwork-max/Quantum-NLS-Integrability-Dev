import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.ThirdConsultation.PDE.BirkhoffInversePolyFinal

/- BIRKHOFF REALIZATION PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORT (no packet
   increment; root-owned BIRKHOFF_REALIZATION record), target NlsGge/ThirdConsultation/PDE/BirkhoffRealization.lean.
   Bodies VERBATIM from Pro r16 L1166-1180: actualBirkhoffMolnar38, actualBirkhoffInput38 := BirkhoffInput38.ofParts …,
   actualBirkhoffInput38_top. Same body shape lane-checked in RealizationCore (2e27812c). Needs ROOT MAIN PROBE. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def actualBirkhoffMolnar38 :
    BirkhoffMolnar38 actualBirkhoffTop38 where
  inverse_polynomial := fun m hm => by
    obtain ⟨C, hC, hbound⟩ :=
      actualBirkhoffTop38_inverse_polynomial m hm
    exact ⟨C, 4 * m - 2, hbound⟩

def actualBirkhoffInput38 : BirkhoffInput38 :=
  BirkhoffInput38.ofParts actualBirkhoffTop38
    actualBirkhoffAnalytic38 actualBirkhoffCanonical38 actualBirkhoffMolnar38

theorem actualBirkhoffInput38_top :
    actualBirkhoffInput38.toBirkhoffTop38 = actualBirkhoffTop38 := rfl

end
end NlsGge.ThirdConsultation.PDE
