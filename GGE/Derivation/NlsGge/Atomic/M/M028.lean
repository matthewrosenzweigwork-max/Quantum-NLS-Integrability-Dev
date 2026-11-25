import Mathlib
import NlsGge.Atomic.M.M026
import NlsGge.ThirdConsultation.M.M028Host
import NlsGge.ThirdConsultation.M.MSchurBound

/-!
# M-028: the off-diagonal Fourier correction bound (proof development, AUTHOR; not self-reviewed)

Head: the design head `STATEMENTS/M.md` (followup9, `schur_offdiagonal_bound`), rebound to the landed round-11 weighted
vocabulary exactly as Pro's round-11 weighted M-024..M-026 heads (section 7.3) rebind the old accessors:
`offDiagonal`, `fourierPotential` are `MTwoMode`'s (with `hlam`); `potentialNorm w phi` is
`MTwoMode.potentialCoefficientNorm w phi`; `TwoModeWeightThreshold w n phi` is the triple
`hw : OneDerivativeWeight w`, `hphi : potentialCoefficientEnergy w phi != top`,
`hthreshold : 8 * potentialCoefficientNorm w phi ^ 2 <= M054.indexWeight n`; the hypothesis-free `weight w (2*n)`
is `w (2*n)`; `<n>` is `M054.indexWeight n`; `componentNorm` is hosted in `M028Host`.
Route: the landed weighted M-026 formula `offDiagonal - fourierPotential = schurEvenRemainder`, then the even path
series bounded termwise by iterating the landed M-022 bound `T_squared_bound` (`MSchurBound`).
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

theorem schur_offdiagonal_bound
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
    w (2 * n) *
        ‖NlsGge.ThirdConsultation.MTwoMode.offDiagonal φ n lam hlam plus -
          NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ plus
            (if plus then 2 * n else -2 * n)‖ ≤
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 *
        NlsGge.ThirdConsultation.M.componentNorm w φ plus /
          NlsGge.Atomic.M.M054.indexWeight n := by
  rw [schur_fourier_remainder_weighted w hw φ hφ n lam hlam hthreshold plus]
  exact NlsGge.ThirdConsultation.MTwoModeB.even_remainder_bound w hw φ hφ n lam hlam hthreshold plus

end NlsGge.ThirdConsultation.M

end
