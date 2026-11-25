import NlsGge.Schur.PhysicalSector

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- Reindex a genuine spectral L² Fourier sum through the actual involution
of the parity sector. This isolates the lower-channel reconstruction goal. -/
lemma hasSum_reflectedSector_fourier
    (n : ℤ) (q : Sector n → ℂ) (f : SpectralScalarL2)
    (hf : HasSum (fun m : Sector n => q m • spectralBasis m.val) f) :
    HasSum (fun m : Sector n => q (negateIndex n m) •
      fourierLp (T := (2 : ℝ)) 2 (-m.val)) f := by
  have hr := (negateEquiv n).hasSum_iff.mpr hf
  change HasSum (fun m : Sector n => q (negateIndex n m) •
    spectralBasis (-m.val)) f at hr
  exact hr

end NlsGge.Schur
