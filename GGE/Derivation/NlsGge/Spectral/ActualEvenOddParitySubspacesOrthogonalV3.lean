import NlsGge.Spectral.ActualHalfTranslationInvolutiveV2
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.Schur

/-- The actual even and odd half-translation eigenspaces are orthogonal. -/
theorem actualEvenOddParitySubspaces_orthogonal_v3
    (x : scalarParity (0 : ℤ)) (y : scalarParity (1 : ℤ)) :
    inner ℂ (x : SpectralScalarL2) (y : SpectralScalarL2) = 0 := by
  have hx : halfTranslation (x : SpectralScalarL2) = (x : SpectralScalarL2) := by
    have h := (mem_scalarParity (0 : ℤ) (x : SpectralScalarL2)).mp x.property
    simpa [spectralSign] using h
  have hy : halfTranslation (y : SpectralScalarL2) = -(y : SpectralScalarL2) := by
    have h := (mem_scalarParity (1 : ℤ) (y : SpectralScalarL2)).mp y.property
    simpa [spectralSign] using h
  have hmap := (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
    (fun z : SpectralCircle => z + ((1 : ℝ) : SpectralCircle))
    halfShift_preserving).inner_map_map
      (x : SpectralScalarL2) (y : SpectralScalarL2)
  change inner ℂ (halfTranslation (x : SpectralScalarL2))
      (halfTranslation (y : SpectralScalarL2)) =
    inner ℂ (x : SpectralScalarL2) (y : SpectralScalarL2) at hmap
  rw [hx, hy, inner_neg_right] at hmap
  have hdouble : (2 : ℂ) *
      inner ℂ (x : SpectralScalarL2) (y : SpectralScalarL2) = 0 := by
    linear_combination -hmap
  exact (mul_eq_zero.mp hdouble).resolve_left (by norm_num)

end NlsGge.Schur

end
