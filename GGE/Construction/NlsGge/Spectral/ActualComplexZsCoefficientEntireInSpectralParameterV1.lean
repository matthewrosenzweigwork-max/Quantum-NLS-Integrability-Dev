import NlsGge.Spectral.FreeZakharovShabatFundamentalComplexV4
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

local instance coefficientComplexMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedAddCommGroup

local instance coefficientComplexMatrixNormedSpace :
    NormedSpace ℂ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedSpace

/-- The coefficient of the spectral parameter in the actual ZS matrix. -/
def zsComplexSpectralSlope : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(-Complex.I), 0; 0, Complex.I]

/-- The source coefficient is affine in the actual complex spectral parameter;
the off-diagonal potential and conjugate-potential terms are unchanged. -/
theorem zsCoefficientComplex_affine_spectral_parameter
    (u : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    zsCoefficientComplex u z t =
      zsCoefficientComplex u 0 t + z • zsComplexSpectralSlope := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zsCoefficientComplex, zsComplexSpectralSlope] <;> ring

/-- The actual matrix coefficient is entire in its complex spectral parameter. -/
theorem analyticOnNhd_zsCoefficientComplex_spectral_parameter
    (u : ℝ → ℂ) (t : ℝ) :
    AnalyticOnNhd ℂ (fun z : ℂ => zsCoefficientComplex u z t) Set.univ := by
  apply AnalyticOnNhd.pi
  intro i
  apply AnalyticOnNhd.pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [zsCoefficientComplex] <;> fun_prop

end NlsGge.SpectralFoundations

end
