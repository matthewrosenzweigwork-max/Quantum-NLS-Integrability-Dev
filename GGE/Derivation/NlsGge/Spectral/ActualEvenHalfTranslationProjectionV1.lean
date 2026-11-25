import NlsGge.Spectral.ActualHalfTranslationInvolutiveV2

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The actual even-parity projection lands in the closed zero-parity
eigenspace. It is the first component-membership step toward the full
period-two parity decomposition. -/
theorem actualEvenHalfTranslationProjection_mem (f : SpectralScalarL2) :
    ((2 : ℂ)⁻¹ • (f + halfTranslation f)) ∈ scalarParity (0 : ℤ) := by
  rw [mem_scalarParity]
  calc
    halfTranslation ((2 : ℂ)⁻¹ • (f + halfTranslation f)) =
        (2 : ℂ)⁻¹ • (halfTranslation f + f) := by
      rw [map_smul, map_add, halfTranslation_involutive_actual_v2]
    _ = spectralSign (0 : ℤ) • ((2 : ℂ)⁻¹ • (f + halfTranslation f)) := by
      simp [spectralSign, smul_smul, add_comm]

end NlsGge.Schur

end
