import Mathlib
import NlsGge.Atomic.M.M025
import NlsGge.ThirdConsultation.M.MW1Power
import NlsGge.ThirdConsultation.M.MW2Diag
import NlsGge.Atomic.KST.KST014

/-!
# M-025: weighted-threshold companion (proof development, AUTHOR; not self-reviewed)

Head: Pro round 11 (`PRO_DEFINITION_RESPONSE_FP80_11.md` section 7.3, `schur_diagonals_equal_weighted`; commit
c7aa9978), printed verbatim.  The landed M-025 packet (`NlsGge.Atomic.M.M025`) carries the local ambient head
`schur_diagonals_equal`; this file adds the weighted companion without touching it.  Route as in M-024/M-026:
`MW1Power.summable_sq_powers_of_weighted` then the norm-free grouped-series proof `MW2Diag`.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

theorem schur_diagonals_equal_weighted
    (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair)
    (hφ :
      NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hthreshold :
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight n) :
    NlsGge.ThirdConsultation.MTwoMode.schurDiagonalPlus φ n lam hlam =
      NlsGge.ThirdConsultation.MTwoMode.schurDiagonalMinus φ n lam hlam :=
  NlsGge.ThirdConsultation.MTwoModeW.schur_diagonals_equal_core_w
    NlsGge.Atomic.KST014.stage14N_grouped_finite_diagonal_eq
    φ n lam hlam
    (NlsGge.ThirdConsultation.MTwoModeW.summable_sq_powers_of_weighted
      w hw φ hφ n lam hlam hthreshold)

end NlsGge.ThirdConsultation.M

end
