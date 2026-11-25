/- T-017 PRODUCTION02 (proof development, AUTHOR; not reviewed). PRODUCTION01 failed only on unknown relativePartition38 (lexical: added open NlsGge.HierarchyRiccati.Core). Target NlsGge/Atomic/T/T017.lean.
   Pro round 6 c5547100 head (PRO_DEFINITION_RESPONSE_FP80_06.md, T-017, binding index packet T-017).
   Route: exact_identity38 (NlsGge/Birkhoff/F11Claim38c.lean, NEW-F11.03) with m = max 2 J.
   B/O-free: exact_identity38 takes no BirkhoffInput38 / OneSmoothingInput38 premise. -/
import Mathlib
import NlsGge.Birkhoff.F11Claim38c

set_option autoImplicit false

open MeasureTheory NlsGge.Pilot NlsGge.Birkhoff
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.T
noncomputable section

theorem finiteChargeTilt_identity
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (J : ℕ) (t : ℕ → ℝ) (ht : TiltAdmissible38 c J t)
    (N : ℕ) :
    Integrable
      (fun u => Real.exp
        (∑ j ∈ Finset.range (J + 1),
          t j * chargeFn38 (max 2 J) j u))
      (nuWN38 c N) ∧
    (∫ u, Real.exp
      (∑ j ∈ Finset.range (J + 1),
        t j * chargeFn38 (max 2 J) j u) ∂nuWN38 c N) =
      (tiltDet38 c J t N)⁻¹ *
        (relativePartition38 (tiltedCoefficients38 c ht) N /
          relativePartition38 c N) :=
  exact_identity38 c ht (max 2 J) (le_max_left 2 J) (le_max_right 2 J) N

end
end NlsGge.ThirdConsultation.T
