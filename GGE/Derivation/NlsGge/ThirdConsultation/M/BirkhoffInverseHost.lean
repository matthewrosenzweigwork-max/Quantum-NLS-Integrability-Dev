import Mathlib
import NlsGge.Atomic.M.M005
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff

/- MBINV HOST PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target NlsGge/ThirdConsultation/M/BirkhoffInverseHost.lean,
   namespace NlsGge.ThirdConsultation.M. Hosts ONLY RealSobolevSequence (followup13 DEFINITIONS/M.lean.md:55) and
   birkhoffInverse (:250-251), bodies VERBATIM. grep NlsGge/ and Work/ (2026-11-02): neither name declared anywhere.
   Consumer: M-049 molnar_inverse_birkhoff. r16 L1149/L1437: birkhoffInverse is the literal G6 inverseBirkhoffSobolev.
   Reused owners: M.SobolevR (Atomic M005), GKDefinitionDesign.inverseBirkhoffSobolev (G6/SobolevBirkhoff). -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M
noncomputable section

abbrev RealSobolevSequence (m : ℕ) := NlsGge.Sobolev38.SobolevCarrier38 (m:ℝ)

def birkhoffInverse (m : ℕ) (z : RealSobolevSequence m) : SobolevR m :=
  NlsGge.GKDefinitionDesign.inverseBirkhoffSobolev m z

end
end NlsGge.ThirdConsultation.M
