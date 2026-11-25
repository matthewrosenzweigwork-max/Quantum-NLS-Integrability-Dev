import Mathlib
import NlsGge.ThirdConsultation.M.M031High
import NlsGge.ThirdConsultation.M.M031Im
import NlsGge.ThirdConsultation.M.M031Low
import NlsGge.ThirdConsultation.M.M031Box

/-!
# M-031: individual localization and an explicit finite central box (proof development, AUTHOR; not self-reviewed)

Heads: Pro round 14 (2d599b57), followup12 STATEMENTS/M.md `M-031`, printed verbatim.
Molnar Theorem 5 (printed p.15, proof pp.21-22):
* thresholded labels: landed label identification at `w := sourceH1Weight` (M031High);
* low labels, real part: the labelling induction split at both thresholded edges `±M`, `M = ⌈8Q² - 1⌉` (M031Low);
* every label, imaginary part: numerical range of the unit-interval ZS eigenproblem, `|Im λ| ≤ (‖φ₁‖∞+‖φ₂‖∞)/2 ≤ Q`
  (M031Im; E1-E4 in M031Num, M031Sup, M031L1);
* uniform head: `N = ⌈8B²⌉₊`, `C = B² + √2 B`, `R = Nπ + C + 8B²π` (M031Box).
The producer obligations (one-derivative weight class, finite source energy) are proved (M031Weight, M031Energy),
not assumed.  No hypothesis beyond the printed heads.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem periodic_spectral_localization
    (φ : KSPS.SobolevC 1) (hW : KSPS.toPotPair φ ∈ gkW) :
    let Q : ℝ := MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ)
    (∀ n : ℤ, 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n →
      ∀ plus : Bool,
        ‖(if plus then lamPlus (KSPS.toPotPair φ) n
          else lamMinus (KSPS.toPotPair φ) n) -
          (n : ℂ) * (Real.pi : ℂ)‖ ≤
          Q ^ 2 / NlsGge.Atomic.M.M054.indexWeight n +
            Real.sqrt 2 * Q / NlsGge.Atomic.M.M054.indexWeight (2 * n)) ∧
    (∀ n : ℤ, NlsGge.Atomic.M.M054.indexWeight n < 8 * Q ^ 2 →
      ∀ plus : Bool,
        let z : ℂ := if plus then lamPlus (KSPS.toPotPair φ) n
          else lamMinus (KSPS.toPotPair φ) n
        |z.re| ≤ (8 * Q ^ 2 - 1 / 2) * Real.pi ∧ |z.im| ≤ Q) :=
  m031_box_of_supports φ hW (periodic_spectral_localization_high φ hW) (low_label_re_bound φ)
    (lamSeq_abs_im_le φ)

theorem periodic_spectral_localization_uniform :
    ∀ B : ℝ, 0 < B →
      ∃ N : ℕ, ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧
      ∀ φ : KSPS.SobolevC 1,
        MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) ≤ B →
        KSPS.toPotPair φ ∈ gkW →
        (∀ n : ℤ, N ≤ n.natAbs → ∀ plus : Bool,
          ‖(if plus then lamPlus (KSPS.toPotPair φ) n
            else lamMinus (KSPS.toPotPair φ) n) -
            (n : ℂ) * (Real.pi : ℂ)‖ ≤
              C / NlsGge.Atomic.M.M054.indexWeight n) ∧
        (∀ n : ℤ, n.natAbs < N → ∀ plus : Bool,
          let z : ℂ := if plus then lamPlus (KSPS.toPotPair φ) n
            else lamMinus (KSPS.toPotPair φ) n
          |z.re| ≤ R ∧ |z.im| ≤ B) :=
  m031_uniform_of_supports periodic_spectral_localization_high low_label_re_bound lamSeq_abs_im_le

end NlsGge.ThirdConsultation.M

end
