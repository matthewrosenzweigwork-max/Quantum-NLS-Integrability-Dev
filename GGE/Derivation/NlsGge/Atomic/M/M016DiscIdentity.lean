import Mathlib
import NlsGge.Atomic.M.M016Step4
import NlsGge.Atomic.M.M016CutFreeConnected
import NlsGge.Atomic.M.M016BaseSign

/- M016 DISCIDENTITY PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M016DiscIdentity.lean. Needs ROOT MAIN PROBE (M016Step4, M016CutFreeConnected absent from mirror).
   * primitive_discriminant_identity_of_S4c: root-requested wrapper; Step 4 with (S4a) discharged by the landed
     `MPrimitive.cutFreeFiber_isPreconnected`, so only (S4c) `hΔ` remains.
   * primitive_discriminant_identity: Pro R16 §1.1 head VERBATIM (L82-88), with (S4c) discharged by
     `M016ChartAux.discrim_lamMinus_zero` (M016BaseSign). No hypotheses beyond the head. -/

set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem primitive_discriminant_identity_of_S4c (φ : PotPair) (hW : φ ∈ gkW)
    (hΔ : NlsGge.GK38.discrim φ (lamMinus φ 0) = 2)
    (z : ℂ) (hz : z ∈ MPrimitive.endpointClosureFiber φ) :
    2 * Complex.cosh (primitive ⟨(φ, z), ⟨hW, hz⟩⟩) = NlsGge.GK38.discrim φ z :=
  primitive_discriminant_identity_of_S4 φ hW (MPrimitive.cutFreeFiber_isPreconnected φ hW) hΔ z hz

theorem primitive_discriminant_identity
    (φ : PotPair) (hW : φ ∈ gkW) (z : ℂ)
    (hz : z ∈ MPrimitive.endpointClosureFiber φ) :
    2 * Complex.cosh (primitive ⟨(φ, z), ⟨hW, hz⟩⟩) =
      NlsGge.GK38.discrim φ z :=
  primitive_discriminant_identity_of_S4c φ hW (M016ChartAux.discrim_lamMinus_zero φ hW) z hz

end NlsGge.ThirdConsultation.M
