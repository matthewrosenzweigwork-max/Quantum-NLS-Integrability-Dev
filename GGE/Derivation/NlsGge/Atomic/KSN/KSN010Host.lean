import Mathlib
import NlsGge.Atomic.G4.G4036Host

set_option autoImplicit false

open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KSN
noncomputable section
open NlsGge.GKDefinitionDesign

def sourceZ (n : ℤ) (a : ℤ) (φ : PotPair) : ℂ :=
  cartesianZExtended n a φ / 2

end
end NlsGge.ThirdConsultation.KSN
