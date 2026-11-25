import Mathlib
import NlsGge.ThirdConsultation.M.M030Bridge
import NlsGge.ThirdConsultation.M.M031Weight
import NlsGge.ThirdConsultation.M.M031Energy

/-!
# M-031 support: the first (thresholded) conjunct of `periodic_spectral_localization` (proof development, AUTHOR; not self-reviewed)

This is NOT the M-031 head.  It is the first conjunct of Pro round 14's `periodic_spectral_localization`
(followup12 STATEMENTS/M.md), printed with the same `let Q` and the same binders `φ : KSPS.SobolevC 1`,
`hW : KSPS.toPotPair φ ∈ gkW`.  Route: landed `periodic_labels_are_local_roots` (M030Bridge) instantiated at
`w := sourceH1Weight`, with the two producer obligations `oneDerivativeWeight_sourceH1Weight` (M031Weight) and
`sourceH1_energy_ne_top` (M031Energy); closed-ball membership is the printed norm inequality.
The second (low-label box) conjunct is open: see M031_STOP.md.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem periodic_spectral_localization_high
    (φ : KSPS.SobolevC 1) (hW : KSPS.toPotPair φ ∈ gkW) :
    let Q : ℝ := MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ)
    ∀ n : ℤ, 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n →
      ∀ plus : Bool,
        ‖(if plus then lamPlus (KSPS.toPotPair φ) n
          else lamMinus (KSPS.toPotPair φ) n) -
          (n : ℂ) * (Real.pi : ℂ)‖ ≤
          Q ^ 2 / NlsGge.Atomic.M.M054.indexWeight n +
            Real.sqrt 2 * Q / NlsGge.Atomic.M.M054.indexWeight (2 * n) := by
  intro Q n hn plus
  obtain ⟨_, _, hm, hp, _, _⟩ := periodic_labels_are_local_roots sourceH1Weight
    oneDerivativeWeight_sourceH1Weight (KSPS.toPotPair φ) hW (sourceH1_energy_ne_top φ) n hn
  cases plus
  · have h := Metric.mem_closedBall.1 hm
    rw [dist_eq_norm] at h
    simpa only [Bool.false_eq_true, ↓reduceIte] using h
  · have h := Metric.mem_closedBall.1 hp
    rw [dist_eq_norm] at h
    simpa only [↓reduceIte] using h

end NlsGge.ThirdConsultation.M

end
