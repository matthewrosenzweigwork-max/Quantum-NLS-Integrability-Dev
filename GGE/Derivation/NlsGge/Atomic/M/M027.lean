import Mathlib
import NlsGge.Atomic.M.M026
import NlsGge.ThirdConsultation.M.MSchurDiag

/-!
# M-027: the Schur diagonal coefficient bound (proof development, AUTHOR; not self-reviewed)

Head: the design head `STATEMENTS/M.md` (followup9, `schur_diagonal_bound`), rebound to the landed round-11 weighted
vocabulary exactly as Pro's round-11 weighted M-024..M-026 heads (section 7.3) rebind the old accessors:
`schurDiagonal` is `MTwoMode.schurDiagonalPlus/Minus` (the two independent diagonal corrections, selected by `plus`,
as in the diagonal clause of `schur_diagonal_odd_formula_weighted`); `potentialNorm w phi` is
`MTwoMode.potentialCoefficientNorm w phi`; `TwoModeWeightThreshold w n phi` is the triple `hw`, `hphi`, `hthreshold`;
`<n>` is `M054.indexWeight n`.  The printed head has no analyticity clause (the packet text does: analyticity is NOT
proved here).
Route: the landed weighted M-026 odd formula `(if plus then Plus else Minus) = schurOddRemainder`, then the odd path
series bounded termwise (`MSchurDiag`): pairing `<e_i, T g>` by Cauchy-Schwarz and `<n> <= |m + 2n| w(m)`, iteration of the
landed M-022 square bound, and `2 ab <= a^2 + b^2` for the two component norms.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

theorem schur_diagonal_bound
    (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair)
    (hφ :
      NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hthreshold :
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight n)
    (plus : Bool) :
    ‖(if plus then
        NlsGge.ThirdConsultation.MTwoMode.schurDiagonalPlus φ n lam hlam
      else
        NlsGge.ThirdConsultation.MTwoMode.schurDiagonalMinus φ n lam hlam)‖ ≤
      NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 /
        NlsGge.Atomic.M.M054.indexWeight n := by
  have h := schur_diagonal_odd_formula_weighted w hw φ hφ n lam hlam hthreshold plus
  obtain ⟨h1, _⟩ := h
  rw [h1]
  exact NlsGge.ThirdConsultation.MTwoModeB.odd_remainder_bound w hw φ hφ n lam hlam hthreshold plus

end NlsGge.ThirdConsultation.M

end
