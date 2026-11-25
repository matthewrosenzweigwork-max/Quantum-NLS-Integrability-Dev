import NlsGge.Spectral.ActualComplexMatrixTwoByTwoEntrySupProductBoundV2
import NlsGge.Spectral.FreeZakharovShabatFundamentalComplexV4

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

theorem actualComplexZsCoefficient_entrySup_bound
    (u : ℝ → ℂ) (z : ℂ) (t R C : ℝ)
    (hz : ‖z‖ ≤ R) (hu : ‖u t‖ ≤ C) :
    actualComplexMatrixEntrySup (zsCoefficientComplex u z t) ≤ R + C := by
  have hC : 0 ≤ C := (norm_nonneg (u t)).trans hu
  have hRnonneg : 0 ≤ R := (norm_nonneg z).trans hz
  have hR : ‖z‖ ≤ R + C := le_trans hz (le_add_of_nonneg_right hC)
  have hU : ‖u t‖ ≤ R + C := le_trans hu (le_add_of_nonneg_left hRnonneg)
  unfold actualComplexMatrixEntrySup
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  · simpa [zsCoefficientComplex] using hR
  · simpa [zsCoefficientComplex] using hU
  · simpa [zsCoefficientComplex] using hU
  · simpa [zsCoefficientComplex] using hR

end NlsGge.SpectralFoundations
