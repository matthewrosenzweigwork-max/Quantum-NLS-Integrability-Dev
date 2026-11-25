import Mathlib
import NlsGge.ThirdConsultation.M.M053Host

/- M-016 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/M/M016Host.lean, namespace NlsGge.ThirdConsultation.M.
   Hosts ONLY `PrimitiveLaurentCoefficients`, body verbatim from followup13 DEFINITIONS/M.lean.md L1966-1979 (Pro round
   16 Q1 "Retain both M-016 heads and the existing body of PrimitiveLaurentCoefficients"). grep NlsGge/ and Work/
   (2026-11-02): not declared anywhere.  NOT hosted here: ExteriorPrimitiveRepresentative (M-052 host, proof development),
   finiteGapPair (complex head only; owner of the complex M-016 head). -/
set_option autoImplicit false
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M
noncomputable section

/-- Finite-order source expansion: H1 has a minus sign, Hk for k≥2 a plus sign. -/
def PrimitiveLaurentCoefficients (N : ℕ) (φ : KSPS.SobolevC N)
    (F : ℂ → ℂ) : Prop :=
  ∀ K : ℕ, 1 ≤ K → K ≤ N + 1 →
    ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧
    ∀ z : ℂ, R ≤ ‖z‖ →
      ‖F z + Complex.I * z +
        hierarchyCharge φ ⟨1, le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩ /
          (2 * Complex.I * z) -
        ∑ k ∈ Finset.Icc 2 K,
          (if hk : 1 ≤ k ∧ k ≤ N + 1 then
            hierarchyCharge φ ⟨k, hk.1, hk.2⟩ /
              (2 * Complex.I * z) ^ k
           else 0)‖ ≤ C / ‖z‖ ^ (K + 1)

end
end NlsGge.ThirdConsultation.M
