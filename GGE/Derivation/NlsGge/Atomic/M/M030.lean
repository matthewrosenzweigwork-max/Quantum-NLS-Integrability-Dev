import Mathlib
import NlsGge.ThirdConsultation.M.M030Roots
import NlsGge.ThirdConsultation.M.M030Bridge
import NlsGge.Atomic.G2.G2046

/-!
# M-030: complex squared gap controlled by the off-diagonal product (proof development, AUTHOR; not self-reviewed)

Head: Pro round 14 (`PRO_DEFINITION_RESPONSE_FP80_14.md`, Cluster 4, M-030; followup12 `STATEMENTS/M.md`), printed
verbatim.  Route: the thresholded label identification `periodic_labels_are_local_roots` (`M030Bridge`/`M030Label`)
discharges the label hypothesis of proof development's `gap_square_schur_bound_of_label_roots` (`M030Roots`: equal diagonals,
Cauchy derivative estimate, root identity).  `GKDefinitionDesign.gap φ n` is by definition `lamPlus φ n - lamMinus φ n`
(G2-046 host).
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem gap_square_schur_bound
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (φ : PotPair)
    (hW : φ ∈ gkW)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ)
    (hthreshold : 8 * MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight n) :
    let P : Set ℝ := {r : ℝ | ∃ z : ℂ,
      ∃ hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n,
        r = ‖MTwoMode.offDiagonal φ n z hz true *
          MTwoMode.offDiagonal φ n z hz false‖}
    P.Nonempty ∧ BddAbove P ∧
    ‖NlsGge.GKDefinitionDesign.gap φ n‖ ^ 2 ≤ 6 * sSup P :=
  gap_square_schur_bound_of_label_roots w hw φ hφ n hthreshold
    (periodic_labels_are_local_roots w hw φ hW hφ n hthreshold)

end NlsGge.ThirdConsultation.M

end
