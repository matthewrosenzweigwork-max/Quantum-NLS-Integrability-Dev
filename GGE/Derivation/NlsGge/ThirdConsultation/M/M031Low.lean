import Mathlib
import NlsGge.ThirdConsultation.M.M030Bridge
import NlsGge.ThirdConsultation.M.M031Weight
import NlsGge.ThirdConsultation.M.M031Energy
import NlsGge.ThirdConsultation.M.M031LowCore

/-!
# M-031 support (A): low-label real-part bound on the source carrier (proof development, AUTHOR; not self-reviewed)

`low_label_re_bound_core` (M031LowCore) at `w := sourceH1Weight`, with the producer obligations
`oneDerivativeWeight_sourceH1Weight`, `sourceH1_energy_ne_top` and the landed bridge
`M030Bridge.perChar_zero_schurDet_zero`.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem low_label_re_bound (φ : KSPS.SobolevC 1) :
    let Q : ℝ := MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ)
    ∀ n : ℤ, NlsGge.Atomic.M.M054.indexWeight n < 8 * Q ^ 2 → ∀ plus : Bool,
      |(if plus then lamPlus (KSPS.toPotPair φ) n else lamMinus (KSPS.toPotPair φ) n).re| ≤
        (8 * Q ^ 2 - 1 / 2) * Real.pi :=
  low_label_re_bound_core sourceH1Weight oneDerivativeWeight_sourceH1Weight (KSPS.toPotPair φ)
    (sourceH1_energy_ne_top φ)
    (fun ψ hψ m hm z hz h0 =>
      perChar_zero_schurDet_zero sourceH1Weight oneDerivativeWeight_sourceH1Weight ψ hψ m hm z hz h0)

end NlsGge.ThirdConsultation.M

end
