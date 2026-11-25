import NlsGge.Spectral.ComplexZsSourcePiPicardScalarPrerequisitesV3
import Mathlib.Analysis.Matrix.Normed

/-!
Minimal normalization between the actual source-Pi matrix norm of `1` and
the real cast of the Picard coefficient.  This isolates the `1 + 1 = 2`
normalization from the local Picard construction.
-/

open scoped NNReal

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

local instance instPicardCoefficientNormSourcePi :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedAddCommGroup

theorem coe_zsPicardRadiusConstant_sourcePiNorm
    (Kcoeff : ℝ≥0) (C : ℝ) (hKcoeff : (Kcoeff : ℝ) = 2 * C) :
    (Kcoeff : ℝ) * (‖(1 : Matrix (Fin 2) (Fin 2) ℂ)‖ + 1) = C * 4 := by
  rw [hKcoeff, norm_one]
  ring

end NlsGge.SpectralFoundations
