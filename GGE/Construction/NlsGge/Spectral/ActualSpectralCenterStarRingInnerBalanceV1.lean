import NlsGge.Schur.FreeCoordinateDomainInverse

set_option autoImplicit false

namespace NlsGge.Schur

/-- Isolate the exact scalar/dictionary balance used in the pointwise formal
symmetry calculation for the actual free diagonal. -/
theorem spectralCenter_starRingEnd_inner_balance
    (n : ℤ) (m : Sector n) (x y : ℂ) :
    starRingEnd ℂ (spectralCenter m.val) * inner ℂ x y =
      inner ℂ x (spectralCenter m.val • y) := by
  have hreal : star (spectralCenter m.val) = spectralCenter m.val := by
    simp [spectralCenter]
  calc
    starRingEnd ℂ (spectralCenter m.val) * inner ℂ x y =
        star (spectralCenter m.val) * inner ℂ x y := by
      simp only [starRingEnd_apply]
    _ = spectralCenter m.val * inner ℂ x y := by rw [hreal]
    _ = inner ℂ x (spectralCenter m.val • y) := by rw [inner_smul_right]

end NlsGge.Schur
