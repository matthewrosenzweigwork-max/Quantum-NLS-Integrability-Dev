import NlsGge.Spectral.ActualEvenHalfTranslationProjectionV1
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- Coherence between the Nat numeral in the carrier and the complex scalar 2. -/
theorem actual_nat_two_smul_complex_scalar_coherence
    (a : ℂ) (f : SpectralScalarL2) :
    a • ((2 : ℕ) • f) = (a * (2 : ℂ)) • f := by
  calc
    a • ((2 : ℕ) • f) = a • (f + f) := by rw [two_nsmul]
    _ = a • f + a • f := by rw [smul_add]
    _ = a • (f + f) := by rw [smul_add]
    _ = a • ((2 : ℂ) • f) := by rw [two_smul]
    _ = (a * (2 : ℂ)) • f := by rw [mul_smul]

end NlsGge.Schur

end
