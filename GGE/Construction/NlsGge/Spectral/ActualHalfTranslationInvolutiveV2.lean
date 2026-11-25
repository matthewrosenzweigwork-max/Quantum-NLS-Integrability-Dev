import NlsGge.Schur.ParityBasis

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The actual half-period translation on doubled-circle L² is an involution.
This is the first operator-side prerequisite for decomposing the full carrier
into the even and odd closed parity subspaces. -/
theorem halfTranslation_involutive_actual_v2 (f : SpectralScalarL2) :
    halfTranslation (halfTranslation f) = f := by
  apply (fourierBasis (T := (2 : ℝ))).repr.injective
  apply lp.ext
  funext m
  rw [halfTranslation_repr, halfTranslation_repr]
  change spectralSign m * (spectralSign m *
    (fourierBasis (T := (2 : ℝ))).repr f m) =
      (fourierBasis (T := (2 : ℝ))).repr f m
  calc
    spectralSign m * (spectralSign m *
        (fourierBasis (T := (2 : ℝ))).repr f m) =
        (spectralSign m * spectralSign m) *
          (fourierBasis (T := (2 : ℝ))).repr f m := by rw [← mul_assoc]
    _ = (fourierBasis (T := (2 : ℝ))).repr f m := by
      rw [spectralSign_mul_self, one_mul]

end NlsGge.Schur

end
