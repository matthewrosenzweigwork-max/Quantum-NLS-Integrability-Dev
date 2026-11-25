import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.Schur

/-- The pointwise algebra behind symmetry of the off-diagonal source
potential on the physical real slice. The source AE conjugacy is proved
separately from the physical L² representatives. -/
theorem actualOffDiagonalPotentialPairingIntegrand
    (u₁ u₂ fPlus fMinus gPlus gMinus : ℂ) (h : u₂ = star u₁) :
    star (u₁ * fMinus) * gPlus + star (u₂ * fPlus) * gMinus =
      star fPlus * (u₁ * gMinus) + star fMinus * (u₂ * gPlus) := by
  rw [h]
  simp only [star_mul, star_star]
  ring

end NlsGge.Schur
