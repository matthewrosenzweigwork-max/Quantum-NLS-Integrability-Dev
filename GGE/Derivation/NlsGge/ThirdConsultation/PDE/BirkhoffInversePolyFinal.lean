import Mathlib
import NlsGge.Atomic.M.M049

/- BIRKHOFF INVERSE POLY FINAL PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORT (no packet
   increment), target NlsGge/ThirdConsultation/PDE/BirkhoffInversePolyFinal.lean. Pro r16 L619-626 head VERBATIM, from
   the M-049 MAIN head (landed `_of` producer, C = 2D). Imports the topological core via M049 → BirkhoffInversePoly,
   never BirkhoffInput38. Needs ROOT MAIN PROBE. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE

theorem actualBirkhoffTop38_inverse_polynomial
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ z : NlsGge.Sobolev38.SobolevCarrier38 (m : ℝ),
        ‖actualBirkhoffTop38.TinvC m z‖ ≤
          C * (1 + ‖z‖) ^ (4 * m - 2) :=
  actualBirkhoffTop38_inverse_polynomial_of m hm (NlsGge.ThirdConsultation.M.molnar_inverse_birkhoff m hm)

end NlsGge.ThirdConsultation.PDE
