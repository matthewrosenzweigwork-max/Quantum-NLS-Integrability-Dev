import NlsGge.Schur.FreeResolvent

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- In coordinates, the actual free resolvent has zero resonant coefficient,
so its output is fixed by the actual complementary Fourier projection. -/
theorem complementarySquare_freeResolventSquare_fixed
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (y : SectorSquare n) :
    complementarySquare n (freeResolventSquare n z hz y) =
      freeResolventSquare n z hz y := by
  apply lp.ext
  funext i
  rw [complementarySquare_apply, freeResolventSquare_apply]
  by_cases hi : i.2 = resonantIndex n
  · simp [hi, freeResolventCoeff]
  · simp [hi]

end NlsGge.Schur
